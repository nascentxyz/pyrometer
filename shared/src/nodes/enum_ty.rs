use crate::AsDotStr;
use crate::analyzer::{GraphLike};
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{EnumDefinition, Identifier, Loc};


/// An index in the graph that references a [`Enum`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct EnumNode(pub usize);

impl AsDotStr for EnumNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("enum {} {{ {} }}",
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
            "..."
        )
    }
}

impl EnumNode {
    /// Gets the underlying node data for the [`Enum`]
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Enum {
        match analyzer.node(*self) {
            Node::Enum(e) => e,
            e => panic!(
                "Node type confusion: expected node to be Contract but it was: {:?}",
                e
            ),
        }
    }

    /// Gets the name of the enum from the underlying node data for the [`Enum`]
    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed contract")
            .name
    }
}

impl From<EnumNode> for NodeIdx {
    fn from(val: EnumNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for EnumNode {
    fn from(idx: NodeIdx) -> Self {
        EnumNode(idx.index())
    }
}

/// A solidity enum representation
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Enum {
    pub loc: Loc,
    pub name: Option<Identifier>,
    pub values: Vec<Option<Identifier>>,
}

impl From<Enum> for Node {
    fn from(val: Enum) -> Self {
        Node::Enum(val)
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
