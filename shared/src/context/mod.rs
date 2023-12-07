use crate::analyzer::GraphError;
use crate::analyzer::{AnalyzerLike, GraphLike, Search};
use crate::as_dot_str;
use crate::nodes::FunctionNode;

use crate::AsDotStr;
use crate::ContractNode;
use crate::FunctionParamNode;
use crate::StructNode;
use petgraph::dot::Dot;
use std::collections::BTreeSet;

use crate::{Edge, Node, NodeIdx};

use solang_parser::pt::Loc;
use std::collections::BTreeMap;

mod var;
pub use var::*;
mod expr_ret;
pub use expr_ret::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum CallFork {
    Call(ContextNode),
    Fork(ContextNode, ContextNode),
}

impl CallFork {
    pub fn maybe_call(&self) -> Option<ContextNode> {
        match self {
            CallFork::Call(c) => Some(*c),
            _ => None,
        }
    }

    pub fn maybe_fork(&self) -> Option<(ContextNode, ContextNode)> {
        match self {
            CallFork::Fork(w1, w2) => Some((*w1, *w2)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ContextEdge {
    // Control flow
    Context,
    Subcontext,
    ContextFork,
    ContextMerge,
    Call,

    // Context Variables
    Variable,
    InheritedVariable,

    AttrAccess,
    Index,
    IndexAccess,
    StructAccess,
    FuncAccess,

    // Variable incoming edges
    Assign,
    StorageAssign,
    MemoryAssign,
    Prev,

    // Control flow
    Return,
    Continue,
    InputVariable,
    ReturnAssign(bool),

    // Range analysis
    Range,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModifierState {
    pub num: usize,
    pub loc: Loc,
    pub parent_fn: FunctionNode,
    pub parent_caller_ctx: ContextNode,
    pub parent_ctx: ContextNode,
    pub renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
}

impl ModifierState {
    pub fn new(
        num: usize,
        loc: Loc,
        parent_fn: FunctionNode,
        parent_ctx: ContextNode,
        parent_caller_ctx: ContextNode,
        renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
    ) -> Self {
        Self {
            num,
            loc,
            parent_fn,
            parent_ctx,
            parent_caller_ctx,
            renamed_inputs,
        }
    }
}

#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct ContextCache {
    pub vars: BTreeMap<String, ContextVarNode>,
    pub visible_funcs: Option<Vec<FunctionNode>>,
    pub first_ancestor: Option<ContextNode>,
    pub associated_source: Option<NodeIdx>,
    pub associated_contract: Option<ContractNode>,
}




// 2023-05-13T04:28:34.318383Z TRACE parse:parse_ctx_stmt_inner:func_call_inner:execute_call_inner:parse_ctx_stmt_inner:parse_ctx_stmt_inner:parse_ctx_expr_inner{ctx=getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }}:fn_call_expr:call_internal_func:func_call_inner:execute_call_inner:parse_ctx_stmt_inner:parse_ctx_stmt_inner: pyrometer::context: Applying to live edges of: getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }._upperBinaryLookup(Checkpoint[], uint32, uint256, uint256).anonymous_fn_call. edges: [
//     "getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }._upperBinaryLookup(Checkpoint[], uint32, uint256, uint256).anonymous_fn_call.average(uint256, uint256).resume{ _upperBinaryLookup(Checkpoint[], uint32, uint256, uint256) }.fork{ true }._unsafeAccess(Checkpoint[], uint256).resume{ _upperBinaryLookup(Checkpoint[], uint32, uint256, uint256) }",
//     "getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }._upperBinaryLookup(Checkpoint[], uint32, uint256, uint256).anonymous_fn_call.average(uint256, uint256).resume{ _upperBinaryLookup(Checkpoint[], uint32, uint256, uint256) }.fork{ false }._unsafeAccess(Checkpoint[], uint256).resume{ _upperBinaryLookup(Checkpoint[], uint32, uint256, uint256) }",
//     "getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }._upperBinaryLookup(Checkpoint[], uint32, uint256, uint256)"
// ]
// 2023-05-13T04:28:34.318505Z TRACE parse:parse_ctx_stmt_inner:func_call_inner:execute_call_inner:parse_ctx_stmt_inner:parse_ctx_stmt_inner:parse_ctx_expr_inner{ctx=getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }}:fn_call_expr:call_internal_func:func_call_inner:execute_call_inner:parse_ctx_stmt_inner:parse_ctx_stmt_inner:advance_var_in_ctx{ctx=getAtProbablyRecentBlock(History, uint256).toUint32(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }.fork{ true }.sqrt(uint256).resume{ getAtProbablyRecentBlock(History, uint256) }._upperBinaryLookup(Checkpoint[], uint32, uint256, uint256)}: pyrometer::context: advancing variable: high
// thread 'main' panicked at 'Variable update of high in old context:
// parent:
// , child: Call(
//     ContextNode(
//         140171,
//     ),
// )'
