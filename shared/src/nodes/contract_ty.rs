use crate::FunctionNode;
use crate::AsDotStr;
use crate::analyzer::Search;
use crate::analyzer::{GraphLike, AnalyzerLike};
use crate::Node;
use crate::NodeIdx;
use crate::Edge;
use solang_parser::pt::{ContractDefinition, ContractTy, Identifier, Loc};


/// An index in the graph that references a [`Contract`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContractNode(pub usize);

impl AsDotStr for ContractNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("{} {}",
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
            e => panic!(
                "Node type confusion: expected node to be Contract but it was: {:?}",
                e
            ),
        }
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
        analyzer.search_children(self.0.into(), &Edge::Func)
        .into_iter()
        .map(FunctionNode::from)
        .collect()
    }

    pub fn associated_source_unit_part(&self, analyzer: &impl GraphLike) -> Option<NodeIdx> {
        analyzer.search_for_ancestor(self.0.into(), &Edge::Contract)
    }

    pub fn associated_source(&self, analyzer: &impl GraphLike) -> Option<NodeIdx> {
        let sup = self.associated_source_unit_part(analyzer)?;
        analyzer.search_for_ancestor(sup, &Edge::Part)
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
        imports: &[(Option<NodeIdx>, String, String, usize)],
        analyzer: &'_ impl AnalyzerLike
    ) -> Contract {
        let mut inherits = vec![];
        con.base.iter().for_each(|base| {
            let inherited_name = &base.name.identifiers[0].name;
            for entry in imports.iter().filter_map(|import| import.0) {
                println!("{:?}", entry);
                for contract in analyzer.search_children(entry, &Edge::Contract).into_iter() {
                    let name = ContractNode::from(contract).name(analyzer);
                    if &name == inherited_name {
                        inherits.push(ContractNode::from(contract));
                        break;
                    }
                }
            }
            
        });
        Contract {
            loc: con.loc,
            ty: con.ty,
            name: con.name,
            inherits
        }
    }
}
