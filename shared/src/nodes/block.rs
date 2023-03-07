use ethers_core::types::Address;
use ethers_core::types::U256;
use ethers_core::types::H256;
use crate::GraphLike;
use crate::analyzer::AsDotStr;
use crate::Node;
use crate::NodeIdx;

/// An index in the graph that references a Block node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct BlockNode(pub usize);

impl BlockNode {
    /// Gets the underlying node data for the block environment
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

/// Represents block-based environment variables available in solidity. These can
/// be set in the configuration (TODO) - if they are not set they are assumed to be
/// in their types default full range (e.g.: `uint256 -> [0, 2**256 - 1]`).
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Block {
    /// The block's hash
    pub hash: Option<H256>,
    /// The block's basefee
    pub basefee: Option<U256>,
    /// The chain id
    pub chainid: Option<U256>,
    /// The block coinbase
    pub coinbase: Option<Address>,
    /// The block difficulty
    pub difficulty: Option<U256>,
    /// The block gas limit
    pub gaslimit: Option<U256>,
    /// The block number
    pub number: Option<U256>,
    /// The block's prevrandao
    pub prevrandao: Option<U256>,
    /// The block's timestamp
    pub timestamp: Option<U256>,
}