use crate::{nodes::Concrete, range::elem::Elem, AsDotStr, GraphBackend, Node};
use shared::{GraphError, NodeIdx, RangeArena};

use alloy_primitives::{Address, B256, U256};

/// An index in the graph that references a Block node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct BlockNode(pub usize);

impl BlockNode {
    /// Gets the underlying node data for the block environment
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Block, GraphError> {
        match analyzer.node(*self) {
            Node::Block(st) => Ok(st),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Msg but it was: {e:?}"
            ))),
        }
    }
}

impl AsDotStr for BlockNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        format!("block {{ {:?} }}", self.underlying(analyzer).unwrap())
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
    pub hash: Option<B256>,
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
    /// The block's blobhash
    pub blobhash: Vec<B256>,
    /// Blob base fee
    pub blobbasefee: Option<U256>,
}
