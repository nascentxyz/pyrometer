use crate::analyzer::Search;
use crate::analyzer::{AnalyzerLike, GraphLike};
use crate::AsDotStr;
use crate::Edge;
use crate::FunctionNode;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{ContractDefinition, ContractTy, Identifier, Loc};

/// An index in the graph that references a [`Contract`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContractNode(pub usize);

impl AsDotStr for ContractNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
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
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Contract {
        match analyzer.node(*self) {
            Node::Contract(func) => func,
            e => panic!("Node type confusion: expected node to be Contract but it was: {e:?}"),
        }
    }

    pub fn inherit(&self, inherits: Vec<String>, analyzer: &mut (impl GraphLike + AnalyzerLike)) {
        let all_contracts = analyzer.search_children(analyzer.entry(), &Edge::Contract);
        inherits.iter().for_each(|inherited_name| {
            let found = all_contracts.iter().find(|contract| {
                &ContractNode::from(**contract).name(analyzer) == inherited_name
            }).unwrap_or_else(|| {analyzer.open_dot(); panic!("Could not find inherited contract: {inherited_name} for contract {:?}", self.name(analyzer)) });
            analyzer.add_edge(*found, *self, Edge::InheritedContract);
        });
    }

    /// Gets the name from the underlying node data for the [`Contract`]
    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed contract")
            .name
    }

    /// Tries to Get the name from the underlying node data for the [`Contract`]
    pub fn maybe_name(&self, analyzer: &'_ impl GraphLike) -> Option<String> {
        let ident = self.underlying(analyzer).name.clone()?;
        Some(ident.name)
    }

    /// Gets the sourcecode location from the underlying node data for the [`Contract`]
    pub fn loc(&self, analyzer: &'_ impl GraphLike) -> Loc {
        self.underlying(analyzer).loc
    }

    /// Gets all associated functions from the underlying node data for the [`Contract`]
    pub fn funcs(&self, analyzer: &'_ (impl GraphLike + Search)) -> Vec<FunctionNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Func)
            .into_iter()
            .map(FunctionNode::from)
            .collect()
    }

    /// Gets all associated modifiers from the underlying node data for the [`Contract`]
    pub fn modifiers(&self, analyzer: &'_ (impl GraphLike + Search)) -> Vec<FunctionNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Modifier)
            .into_iter()
            .map(FunctionNode::from)
            .collect()
    }

    pub fn associated_source_unit_part(&self, analyzer: &impl GraphLike) -> NodeIdx {
        analyzer
            .search_for_ancestor(self.0.into(), &Edge::Contract)
            .expect("detached contract")
    }

    pub fn associated_source(&self, analyzer: &impl GraphLike) -> NodeIdx {
        let sup = self.associated_source_unit_part(analyzer);
        analyzer
            .search_for_ancestor(sup, &Edge::Part)
            .expect("detached source unit part")
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
        imports: &[(Option<NodeIdx>, String, String, usize)],
        analyzer: &'_ impl AnalyzerLike,
    ) -> (Contract, Vec<String>) {
        let mut inherits = vec![];
        let mut unhandled_inherits = vec![];
        con.base.iter().for_each(|base| {
            let inherited_name = &base.name.identifiers[0].name;
            let mut found = false;
            for contract in analyzer.search_children(source, &Edge::Contract).into_iter() {
                let name = ContractNode::from(contract).name(analyzer);
                if &name == inherited_name {
                    inherits.push(ContractNode::from(contract));
                    found = true;
                    break;
                }
            }

            if !found {
                for entry in imports.iter().filter_map(|import| import.0) {
                    for contract in analyzer.search_children(entry, &Edge::Contract).into_iter() {
                        let name = ContractNode::from(contract).name(analyzer);
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
            },
            unhandled_inherits
        )
    }
}
