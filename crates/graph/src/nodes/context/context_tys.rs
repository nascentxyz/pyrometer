
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