use crate::{
    nodes::{FunctionNode, SourceUnitNode, SourceUnitPartNode, StructNode, VarNode},
    AnalyzerBackend, AsDotStr, Edge, GraphBackend, GraphError, Node,
};
use shared::{NodeIdx, Search};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{ContractDefinition, ContractTy, Identifier, Loc};

use std::collections::BTreeMap;

/// An index in the graph that references a [`Contract`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContractNode(pub usize);

impl AsDotStr for ContractNode {
    fn as_dot_str(&self, analyzer: &impl GraphBackend) -> String {
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
            analyzer.add_edge(*found, *self, Edge::InheritedContract);
        });
    }

    pub fn direct_inherited_contracts(&self, analyzer: &impl GraphBackend) -> Vec<ContractNode> {
        self.underlying(analyzer).unwrap().inherits.clone()
    }

    pub fn all_inherited_contracts(&self, analyzer: &impl GraphBackend) -> Vec<ContractNode> {
        let mut inherits = self.direct_inherited_contracts(analyzer);
        inherits.extend(
            inherits
                .iter()
                .flat_map(|i| i.direct_inherited_contracts(analyzer))
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
            .search_children_depth(self.0.into(), &Edge::Func, 1, 0)
            .into_iter()
            .map(FunctionNode::from)
            .collect()
    }

    pub fn constructor(&self, analyzer: &(impl GraphBackend + Search)) -> Option<FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Constructor, 1, 0)
            .into_iter()
            .map(FunctionNode::from)
            .take(1)
            .next()
    }

    /// Gets all associated storage vars from the underlying node data for the [`Contract`]
    pub fn direct_storage_vars(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<VarNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Var, 1, 0)
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
        analyzer: &(impl Search + AnalyzerBackend),
    ) -> BTreeMap<String, FunctionNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Func, 1, 0)
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
    ) -> Result<BTreeMap<String, FunctionNode>, GraphError> {
        if let Some(funcs) = &self.underlying(analyzer)?.cached_functions {
            Ok(funcs.clone())
        } else {
            let mut mapping = self.funcs_mapping(analyzer);
            self.direct_inherited_contracts(analyzer)
                .iter()
                .for_each(|inherited| {
                    inherited
                        .linearized_functions(analyzer)
                        .unwrap()
                        .iter()
                        .for_each(|(name, func)| {
                            if !mapping.contains_key(name) {
                                mapping.insert(name.to_string(), *func);
                            }
                        });
                });
            self.underlying_mut(analyzer)?.cached_functions = Some(mapping.clone());
            Ok(mapping)
        }
    }

    pub fn structs(&self, analyzer: &(impl GraphBackend + Search)) -> Vec<StructNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Struct, 1, 0)
            .into_iter()
            .map(StructNode::from)
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
    /// A list of contracts that this contract inherits (TODO: inheritance linearization)
    pub inherits: Vec<ContractNode>,
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
        let mut inherits = vec![];
        let mut unhandled_inherits = vec![];
        con.base.iter().for_each(|base| {
            let inherited_name = &base.name.identifiers[0].name;
            let mut found = false;
            for contract in analyzer
                .search_children_exclude_via(source, &Edge::Contract, &[Edge::Func])
                .into_iter()
            {
                let name = ContractNode::from(contract).name(analyzer).unwrap();
                if &name == inherited_name {
                    inherits.push(ContractNode::from(contract));
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
                            inherits.push(ContractNode::from(contract));
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
        (
            Contract {
                loc: con.loc,
                ty: con.ty,
                name: con.name,
                inherits,
                cached_functions: None,
            },
            unhandled_inherits,
        )
    }
}
