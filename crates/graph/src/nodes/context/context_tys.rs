use crate::nodes::{ContextNode, ContextVarNode, ContractNode, FunctionNode, StructNode};
use shared::NodeIdx;

use solang_parser::pt::Loc;

use std::collections::BTreeMap;

/// An enum that denotes either a call or a fork of a context
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum CallFork {
    Call(ContextNode),
    Fork(ContextNode, ContextNode),
}

impl CallFork {
    /// Returns an option of the call context
    pub fn maybe_call(&self) -> Option<ContextNode> {
        match self {
            CallFork::Call(c) => Some(*c),
            _ => None,
        }
    }

    /// Returns an option of the two fork contexts
    pub fn maybe_fork(&self) -> Option<(ContextNode, ContextNode)> {
        match self {
            CallFork::Fork(w1, w2) => Some((*w1, *w2)),
            _ => None,
        }
    }
}

/// Holds the current modifier state
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModifierState {
    /// The number of the current modifier being evaluated
    pub num: usize,
    /// The location in source
    pub loc: Loc,
    /// The calling function
    pub parent_fn: FunctionNode,
    /// The context of the caller to the function that had this modifier
    pub parent_caller_ctx: ContextNode,
    /// The parent context
    pub parent_ctx: ContextNode,
    /// Renamed inputs based on the modifier
    pub renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
    pub try_catch: bool,
}

impl ModifierState {
    /// Constructs a modifier state
    pub fn new(
        num: usize,
        loc: Loc,
        parent_fn: FunctionNode,
        parent_ctx: ContextNode,
        parent_caller_ctx: ContextNode,
        renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
        try_catch: bool,
    ) -> Self {
        Self {
            num,
            loc,
            parent_fn,
            parent_ctx,
            parent_caller_ctx,
            renamed_inputs,
            try_catch,
        }
    }
}

/// Holds cached information about the context to speed up lookups
#[derive(Default, Debug, Clone, Eq, PartialEq)]
pub struct ContextCache {
    /// Variables in this context
    pub vars: BTreeMap<String, ContextVarNode>,
    /// Storage variables in this context - they may have been shadowed so we need to keep track of them
    /// separately
    pub storage_vars: BTreeMap<String, ContextVarNode>,
    /// Temporary variables in this context
    pub tmp_vars: BTreeMap<String, ContextVarNode>,
    /// Visible functions from this context
    pub visible_funcs: Option<Vec<FunctionNode>>,
    /// Visible structs from this context
    pub visible_structs: Option<Vec<StructNode>>,
    /// First ancestor of this context
    pub first_ancestor: Option<ContextNode>,
    /// Associated source of this context
    pub associated_source: Option<NodeIdx>,
    /// Associated contract of this context
    pub associated_contract: Option<ContractNode>,
}
