use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{EnumDefinition, Identifier, Loc};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct EnumNode(pub usize);

impl Into<NodeIdx> for EnumNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for EnumNode {
    fn from(idx: NodeIdx) -> Self {
        EnumNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Enum {
    pub loc: Loc,
    pub name: Option<Identifier>,
    pub values: Vec<Option<Identifier>>,
}

impl Into<Node> for Enum {
    fn into(self) -> Node {
        Node::Enum(self)
    }
}

impl From<EnumDefinition> for Enum {
    fn from(enu: EnumDefinition) -> Enum {
        Enum {
            loc: enu.loc,
            name: enu.name,
            values: enu.values,
        }
    }
}
