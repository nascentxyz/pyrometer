use ethers_core::types::Address;
use ethers_core::types::U256;
use ethers_core::types::H256;
use crate::GraphLike;
use crate::analyzer::AsDotStr;
use crate::Node;
use crate::NodeIdx;


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct BlockNode(pub usize);

impl BlockNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Block {
        match analyzer.node(*self) {
            Node::Block(st) => st,
            e => panic!(
                "Node type confusion: expected node to be Msg but it was: {:?}",
                e
            ),
        }
    }
}

impl AsDotStr for BlockNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("block {{ {:?} }}", self.underlying(analyzer))
    }
}

impl From<BlockNode> for NodeIdx {
    fn from(val: BlockNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for BlockNode {
    fn from(idx: NodeIdx) -> Self {
        BlockNode(idx.index())
    }
}


#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Block {
    pub hash: H256,
    pub basefee: U256,
    pub chainid: U256,
    pub coinbase: Address,
    pub difficulty: U256,
    pub gaslimit: U256,
    pub number: U256,
    pub prevrandao: U256,
    pub timestamp: U256,
}