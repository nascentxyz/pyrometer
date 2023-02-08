use ethers_core::types::Address;
use ethers_core::types::U256;
use crate::GraphLike;
use crate::analyzer::AsDotStr;
use crate::Node;
use crate::NodeIdx;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct MsgNode(pub usize);

impl MsgNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Msg {
        match analyzer.node(*self) {
            Node::Msg(st) => st,
            e => panic!(
                "Node type confusion: expected node to be Msg but it was: {:?}",
                e
            ),
        }
    }
}


impl AsDotStr for MsgNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("msg {{ {:?} }}", self.underlying(analyzer))
    }
}

impl From<MsgNode> for NodeIdx {
    fn from(val: MsgNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for MsgNode {
    fn from(idx: NodeIdx) -> Self {
        MsgNode(idx.index())
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Msg {
    pub data: Option<Vec<u8>>,
    pub sender: Option<Address>,
    pub sig: Option<[u8; 4]>,
    pub value: Option<U256>,
    pub origin: Option<Address>,
    pub gasprice: Option<U256>,
    pub gaslimit: Option<U256>,
}


