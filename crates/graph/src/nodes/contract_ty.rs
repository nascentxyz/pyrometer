use crate::{
    nodes::{
        Concrete, EnumNode, ErrorNode, FunctionNode, SourceUnitNode, SourceUnitPartNode,
        StructNode, TyNode, VarNode,
    },
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, Edge, GraphBackend, Node,
};
use shared::{GraphError, NodeIdx, RangeArena, Search};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{ContractDefinition, ContractTy, Identifier, Loc};

use std::collections::BTreeMap;

/// An index in the graph that references a [`Contract`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContractNode(pub usize);

impl AsDotStr for ContractNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "{} {}",
            underlying.ty,
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
        )
    }
}

impl ContractNode {
    /// Gets the underlying node data for the [`Contract`]
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Contract, GraphError> {
        match analyzer.node(*self) {
            Node::Contract(contract) => Ok(contract),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Contract but it was: {e:?}"
            ))),
        }
    }

    /// Gets the underlying node data for the [`Contract`] as mutable
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut Contract, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Contract(contract) => Ok(contract),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Contract but it was: {e:?}"
            ))),
        }
    }

    pub fn super_contracts(&self, analyzer: &impl GraphBackend) -> Vec<ContractNode> {
        analyzer
            .graph()
            .edges_directed((*self).into(), Direction::Incoming)
            .filter(|edge| edge.weight() == &Edge::InheritedContract)
            .map(|edge| ContractNode::from(edge.source()))
            .collect()
    }

    pub fn inherit(&self, inherits: Vec<String>, analyzer: &mut impl AnalyzerBackend) {
        let src = self.associated_source(analyzer);
        let all_contracts = analyzer.search_children_include_via(
            src.into(),
            &Edge::Contract,
            &[
                Edge::Import,
                Edge::Part,
                Edge::Contract,
                Edge::InheritedContract,
            ],
        );
        // we unwrap the name call because we dont really wanna bubble up thru an iteration
        inherits.iter().for_each(|inherited_name| {
            let found = all_contracts
                .iter()
                .find(|contract| {
                    &ContractNode::from(**contract).name(analyzer).unwrap() == inherited_name
                })
                .unwrap_or_else(|| {
                    panic!(
                        "Could not find inherited contract: {inherited_name} for contract {:?}",
                        self.name(analyzer)
                    )
                });
            self.underlying_mut(analyzer)
                .unwrap()
                .inherits
                .push(Some(ContractNode::from(*found)));
            analyzer.add_edge(*found, *self, Edge::InheritedContract);
        });
        self.order_inherits(analyzer);
    }

    pub fn order_inherits(&self, analyzer: &mut impl AnalyzerBackend) {
        let raw_inherits = self.underlying(analyzer).unwrap().raw_inherits.clone();
        let inherits = self.underlying(analyzer).unwrap().inherits.clone();

        let mut tmp_inherits = vec![];
        tmp_inherits.resize(inherits.len(), None);
        inherits.into_iter().for_each(|inherited| {
            if let Some(inherited) = inherited {
                let i_name = inherited.name(analyzer).unwrap();
                let position = raw_inherits.iter().position(|raw| &i_name == raw).unwrap();
                tmp_inherits[position] = Some(inherited);
            }
        });
        self.underlying_mut(analyzer).unwrap().inherits = tmp_inherits;
    }

    pub fn direct_inherited_contracts(&self, analyzer: &impl GraphBackend) -> Vec<ContractNode> {
        self.underlying(analyzer)
            .unwrap()
            .inherits
            .iter()
            .filter_map(|i| i.as_ref())
            .cloned()
            .collect()
    }

    pub fn all_inherited_contracts(&self, analyzer: &impl GraphBackend) -> Vec<ContractNode> {
        let mut inherits = self.direct_inherited_contracts(analyzer);
        inherits.extend(
            inherits
                .iter()
                .flat_map(|i| i.all_inherited_contracts(analyzer))
                .collect::<Vec<_>>(),
        );
        inherits.into_iter().collect::<Vec<_>>()
    }

    /// Gets the name from the underlying node data for the [`Contract`]
    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .name
            .clone()
            .expect("Unnamed contract")
            .name)
    }

    /// Tries to Get the name from the underlying node data for the [`Contract`]
    pub fn maybe_name(&self, analyzer: &impl GraphBackend) -> Result<Option<String>, GraphError> {
        if let Some(ident) = self.underlying(analyzer)?.name.clone() {
            Ok(Some(ident.name))
        } else {
            Ok(None)
        }
    }

    /// Gets the sourcecode location from the underlying node data for the [`Contract`]
    pub fn loc(&self, analyzer: &impl GraphBackend) -> Result<Loc, GraphError> {
        Ok(self.underlying(analyzer)?.loc)
    }

    /// Gets all associated functions from the underlying node data for the [`Contract`]
    pub fn funcs(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Func, 0, 0)
            .into_iter()
            .map(FunctionNode::from)
            .collect()
    }

    pub fn constructor(&self, analyzer: &(impl GraphBackend + Search)) -> Option<FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Constructor, 0, 0)
            .into_iter()
            .map(FunctionNode::from)
            .take(1)
            .next()
    }

    pub fn ordered_new_param_names(&self, analyzer: &impl GraphBackend) -> Vec<String> {
        if let Some(constructor) = self.constructor(analyzer) {
            constructor.ordered_param_names(analyzer)
        } else {
            vec![]
        }
    }

    /// Gets all associated storage vars from the underlying node data for the [`Contract`]
    pub fn direct_storage_vars(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<VarNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Var, 0, 0)
            .into_iter()
            .map(VarNode::from)
            .collect()
    }

    /// Gets all associated storage vars from the underlying node data for the [`Contract`]
    pub fn all_storage_vars(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<VarNode> {
        let mut ret = self
            .all_inherited_contracts(analyzer)
            .iter()
            .flat_map(|contract| contract.direct_storage_vars(analyzer))
            .collect::<Vec<_>>();
        ret.extend(self.direct_storage_vars(analyzer));
        ret
    }

    pub fn funcs_mapping(
        &self,
        analyzer: &mut (impl Search + AnalyzerBackend),
    ) -> BTreeMap<String, FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Func, 0, 0)
            .into_iter()
            .map(|i| {
                let fn_node = FunctionNode::from(i);
                (fn_node.name(analyzer).unwrap(), fn_node)
            })
            .collect::<BTreeMap<String, FunctionNode>>()
    }

    pub fn linearized_functions(
        &self,
        analyzer: &mut (impl Search + AnalyzerBackend),
        super_func: bool,
    ) -> Result<BTreeMap<String, FunctionNode>, GraphError> {
        if !super_func {
            if let Some(funcs) = &self.underlying(analyzer)?.cached_functions {
                return Ok(funcs.clone());
            }
        }

        let mut mapping = if !super_func {
            self.funcs_mapping(analyzer)
        } else {
            Default::default()
        };
        self.direct_inherited_contracts(analyzer)
            .iter()
            .for_each(|inherited| {
                inherited
                    .linearized_functions(analyzer, false)
                    .unwrap()
                    .iter()
                    .for_each(|(name, func)| {
                        if !mapping.contains_key(name) {
                            mapping.insert(name.to_string(), *func);
                        }
                    });
            });
        if !super_func {
            self.underlying_mut(analyzer)?.cached_functions = Some(mapping.clone());
        }
        Ok(mapping)
    }

    pub fn structs(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<StructNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Struct, 0, 0)
            .into_iter()
            .map(StructNode::from)
            .collect()
    }

    pub fn enums(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<EnumNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Enum, 0, 0)
            .into_iter()
            .map(EnumNode::from)
            .collect()
    }

    pub fn tys(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<TyNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Ty, 0, 0)
            .into_iter()
            .map(TyNode::from)
            .collect()
    }

    pub fn errs(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<ErrorNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Error, 0, 0)
            .into_iter()
            .map(ErrorNode::from)
            .collect()
    }

    pub fn visible_structs(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<StructNode> {
        let mut structs = self.structs(analyzer);
        let inherited = self.all_inherited_contracts(analyzer);
        structs.extend(
            inherited
                .iter()
                .flat_map(|c| c.structs(analyzer))
                .collect::<Vec<_>>(),
        );
        structs
    }

    pub fn visible_enums(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<EnumNode> {
        let mut enums = self.enums(analyzer);
        let inherited = self.all_inherited_contracts(analyzer);
        enums.extend(
            inherited
                .iter()
                .flat_map(|c| c.enums(analyzer))
                .collect::<Vec<_>>(),
        );
        enums
    }

    pub fn visible_errors(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<ErrorNode> {
        let mut errors = self.errs(analyzer);
        let inherited = self.all_inherited_contracts(analyzer);
        errors.extend(
            inherited
                .iter()
                .flat_map(|c| c.errs(analyzer))
                .collect::<Vec<_>>(),
        );
        errors
    }

    pub fn visible_tys(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<TyNode> {
        let mut tys = self.tys(analyzer);
        let inherited = self.all_inherited_contracts(analyzer);
        tys.extend(
            inherited
                .iter()
                .flat_map(|c| c.tys(analyzer))
                .collect::<Vec<_>>(),
        );
        tys
    }

    pub fn visible_local_nodes(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<NodeIdx> {
        let mut nodes = self
            .structs(analyzer)
            .iter()
            .map(|i| i.0.into())
            .collect::<Vec<_>>();
        nodes.extend(self.enums(analyzer).iter().map(|i| NodeIdx::from(i.0)));
        nodes.extend(self.tys(analyzer).iter().map(|i| NodeIdx::from(i.0)));
        nodes.extend(self.errs(analyzer).iter().map(|i| NodeIdx::from(i.0)));
        nodes.extend(
            self.direct_storage_vars(analyzer)
                .iter()
                .map(|i| NodeIdx::from(i.0)),
        );
        nodes
    }

    pub fn visible_nodes(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<NodeIdx> {
        let mut nodes = self.visible_local_nodes(analyzer);
        let inherited = self.all_inherited_contracts(analyzer);
        nodes.extend(
            inherited
                .iter()
                .flat_map(|c| c.visible_local_nodes(analyzer)),
        );
        nodes
    }

    /// Gets all associated modifiers from the underlying node data for the [`Contract`]
    pub fn modifiers(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Modifier, 1, 0)
            .into_iter()
            .map(FunctionNode::from)
            .collect()
    }

    pub fn associated_source_unit_part(
        &self,
        analyzer: &(impl GraphBackend + Search),
    ) -> SourceUnitPartNode {
        analyzer
            .search_for_ancestor(self.0.into(), &Edge::Contract)
            .expect("detached contract")
            .into()
    }

    pub fn associated_source(&self, analyzer: &(impl GraphBackend + Search)) -> SourceUnitNode {
        let sup = self.associated_source_unit_part(analyzer);
        analyzer
            .search_for_ancestor(sup.into(), &Edge::Part)
            .expect("detached source unit part")
            .into()
    }
}

impl From<ContractNode> for NodeIdx {
    fn from(val: ContractNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContractNode {
    fn from(idx: NodeIdx) -> Self {
        ContractNode(idx.index())
    }
}

/// A solidity contract representation
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Contract {
    /// Sourcecode location
    pub loc: Loc,
    /// The type of contract
    pub ty: ContractTy,
    /// An optional name in the form of an identifier (`(Loc, String)`)
    pub name: Option<Identifier>,
    /// Raw inherited strings, ordered by least base to most base
    pub raw_inherits: Vec<String>,
    /// A list of contracts that this contract inherits (TODO: inheritance linearization)
    pub inherits: Vec<Option<ContractNode>>,
    /// Cached linearized functions
    pub cached_functions: Option<BTreeMap<String, FunctionNode>>,
}

impl From<Contract> for Node {
    fn from(val: Contract) -> Self {
        Node::Contract(val)
    }
}

impl Contract {
    /// Constructs a new contract from a `ContractDefinition` with imports
    pub fn from_w_imports(
        con: ContractDefinition,
        source: NodeIdx,
        imports: &[Option<NodeIdx>],
        analyzer: &impl GraphBackend,
    ) -> (Contract, Vec<String>) {
        let mut raw_inherits = vec![];
        let mut inherits = vec![];
        let mut unhandled_inherits = vec![];
        con.base.iter().for_each(|base| {
            let inherited_name = &base.name.identifiers[0].name;
            raw_inherits.push(inherited_name.clone());
            let mut found = false;
            for contract in analyzer
                .search_children_exclude_via(source, &Edge::Contract, &[Edge::Func])
                .into_iter()
            {
                let name = ContractNode::from(contract).name(analyzer).unwrap();
                if &name == inherited_name {
                    inherits.push(Some(ContractNode::from(contract)));
                    found = true;
                    break;
                }
            }

            if !found {
                for entry in imports.iter().filter_map(|&import| import) {
                    for contract in analyzer
                        .search_children_exclude_via(entry, &Edge::Contract, &[Edge::Func])
                        .into_iter()
                    {
                        let name = ContractNode::from(contract).name(analyzer).unwrap();
                        if &name == inherited_name {
                            inherits.push(Some(ContractNode::from(contract)));
                            found = true;
                            break;
                        }
                    }
                }
            }

            if !found {
                unhandled_inherits.push(inherited_name.clone());
            }
        });

        raw_inherits.reverse();
        let mut this = Contract {
            loc: con.loc,
            ty: con.ty,
            name: con.name,
            raw_inherits,
            inherits,
            cached_functions: None,
        };

        this.order_inherits(analyzer);
        (this, unhandled_inherits)
    }

    pub fn order_inherits(&mut self, analyzer: &impl GraphBackend) {
        let raw_inherits = self.raw_inherits.clone();
        let inherits = self.inherits.clone();

        let mut tmp_inherits = vec![];
        tmp_inherits.resize(raw_inherits.len(), None);
        inherits.into_iter().for_each(|inherited| {
            if let Some(inherited) = inherited {
                let i_name = inherited.name(analyzer).unwrap();
                let position = raw_inherits.iter().position(|raw| &i_name == raw).unwrap();
                tmp_inherits[position] = Some(inherited);
            }
        });
        self.inherits = tmp_inherits;
    }
}
