use crate::analyzer::AnalyzerLike;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{ContractDefinition, ContractTy, Identifier, Loc};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContractNode(pub usize);
impl ContractNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Contract {
        match analyzer.node(*self) {
            Node::Contract(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Contract but it was: {:?}",
                e
            ),
        }
    }

    pub fn name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed contract")
            .name
    }
}
impl Into<NodeIdx> for ContractNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for ContractNode {
    fn from(idx: NodeIdx) -> Self {
        ContractNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Contract {
    pub loc: Loc,
    pub ty: ContractTy,
    pub name: Option<Identifier>,
}

impl Into<Node> for Contract {
    fn into(self) -> Node {
        Node::Contract(self)
    }
}

impl From<ContractDefinition> for Contract {
    fn from(con: ContractDefinition) -> Contract {
        Contract {
            loc: con.loc,
            ty: con.ty,
            name: con.name,
        }
    }
}
