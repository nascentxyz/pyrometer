use crate::{
    nodes::{
        CallFork, ContextCache, ContextNode, ContextVarNode, ExprRet, FunctionNode, KilledKind,
        ModifierState,
    },
    solvers::dl::DLSolver,
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use shared::{ExprFlag, GraphError, NodeIdx};

use solang_parser::pt::Loc;
use std::collections::BTreeSet;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum SubContextKind {
    InternalFnCall {
        caller_ctx: ContextNode,
        return_into_ctx: ContextNode,
        fn_called: FunctionNode,
    },
    ExternalFnCall {
        caller_ctx: ContextNode,
        return_into_ctx: ContextNode,
        fn_called: FunctionNode,
    },
    Loop {
        parent_ctx: ContextNode,
    },
    Fork {
        parent_ctx: ContextNode,
        true_side: bool,
    },
    FnReturn {
        from_fn_call_ctx: ContextNode,
        continuation_of: ContextNode,
    },
    Dummy {
        parent_ctx: ContextNode,
    },
}

impl SubContextKind {
    pub fn new_fork(parent_ctx: ContextNode, true_side: bool) -> Self {
        SubContextKind::Fork {
            parent_ctx,
            true_side,
        }
    }

    pub fn new_fn_ret(from_fn_call_ctx: ContextNode, continuation_of: ContextNode) -> Self {
        SubContextKind::FnReturn {
            from_fn_call_ctx,
            continuation_of,
        }
    }

    pub fn new_dummy(parent_ctx: ContextNode) -> Self {
        SubContextKind::Dummy { parent_ctx }
    }

    pub fn new_loop(parent_ctx: ContextNode) -> Self {
        SubContextKind::Loop { parent_ctx }
    }

    pub fn new_fn_call(
        caller_ctx: ContextNode,
        return_into_ctx: Option<ContextNode>,
        fn_called: FunctionNode,
        is_ext: bool,
    ) -> Self {
        let return_into_ctx = return_into_ctx.unwrap_or(caller_ctx);
        if is_ext {
            SubContextKind::ExternalFnCall {
                caller_ctx,
                return_into_ctx,
                fn_called,
            }
        } else {
            SubContextKind::InternalFnCall {
                caller_ctx,
                return_into_ctx,
                fn_called,
            }
        }
    }

    pub fn parent_ctx(&self) -> ContextNode {
        match self {
            SubContextKind::InternalFnCall {
                caller_ctx: parent_ctx,
                ..
            }
            | SubContextKind::ExternalFnCall {
                caller_ctx: parent_ctx,
                ..
            }
            | SubContextKind::FnReturn {
                from_fn_call_ctx: parent_ctx,
                ..
            }
            | SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Dummy { parent_ctx }
            | SubContextKind::Loop { parent_ctx } => *parent_ctx,
        }
    }

    pub fn path_ext(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        Ok(match self {
            SubContextKind::ExternalFnCall { fn_called, .. } => {
                let name = fn_called.name(analyzer)?;
                format!("{{ {name} }}")
            }
            SubContextKind::InternalFnCall { fn_called, .. } => {
                let name = fn_called.name(analyzer)?;
                format!("{{ {name} }}")
            }
            SubContextKind::Fork { true_side, .. } => format!("fork{{ {true_side} }}"),
            SubContextKind::FnReturn {
                continuation_of, ..
            } => format!(
                "resume{{ {} }}",
                continuation_of.associated_fn(analyzer)?.name(analyzer)?
            ),
            SubContextKind::Loop { .. } => "loop".to_string(),
            SubContextKind::Dummy { .. } => "<dummy>".to_string(),
        })
    }

    pub fn init_ctx_deps(
        &self,
        analyzer: &impl AnalyzerBackend,
    ) -> Result<BTreeSet<ContextVarNode>, GraphError> {
        Ok(self.parent_ctx().underlying(analyzer)?.ctx_deps.clone())
    }

    pub fn init_expr_ret_stack(
        &self,
        analyzer: &impl AnalyzerBackend,
    ) -> Result<Vec<ExprRet>, GraphError> {
        Ok(match self {
            SubContextKind::Fork { parent_ctx, .. } | SubContextKind::Loop { parent_ctx } => {
                parent_ctx.underlying(analyzer)?.expr_ret_stack.clone()
            }
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of.underlying(analyzer)?.expr_ret_stack.clone(),
            _ => vec![],
        })
    }

    pub fn fn_call(&self) -> Option<FunctionNode> {
        match self {
            SubContextKind::ExternalFnCall { fn_called, .. } => Some(*fn_called),
            SubContextKind::InternalFnCall { fn_called, .. } => Some(*fn_called),
            SubContextKind::Fork { .. }
            | SubContextKind::Loop { .. }
            | SubContextKind::Dummy { .. }
            | SubContextKind::FnReturn { .. } => None,
        }
    }

    pub fn init_parse_idx(&self, analyzer: &impl AnalyzerBackend) -> usize {
        match self {
            SubContextKind::ExternalFnCall { .. } => 0,
            SubContextKind::InternalFnCall { .. } => 0,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => parent_ctx.parse_idx(analyzer),
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of.parse_idx(analyzer),
        }
    }

    pub fn init_expr_flag(&self, analyzer: &impl AnalyzerBackend) -> Option<ExprFlag> {
        match self {
            SubContextKind::ExternalFnCall { .. } => None,
            SubContextKind::InternalFnCall { .. } => None,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => parent_ctx.peek_expr_flag(analyzer),
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of.peek_expr_flag(analyzer),
        }
    }

    pub fn init_ctx_cache(
        &self,
        analyzer: &impl AnalyzerBackend,
    ) -> Result<ContextCache, GraphError> {
        let visible_funcs = match self {
            SubContextKind::ExternalFnCall { .. } => None,
            SubContextKind::InternalFnCall { .. } => None,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => {
                parent_ctx.underlying(analyzer)?.cache.visible_funcs.clone()
            }
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of
                .underlying(analyzer)?
                .cache
                .visible_funcs
                .clone(),
        };

        let visible_structs = match self {
            SubContextKind::ExternalFnCall { .. } => None,
            SubContextKind::InternalFnCall { .. } => None,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => parent_ctx
                .underlying(analyzer)?
                .cache
                .visible_structs
                .clone(),
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of
                .underlying(analyzer)?
                .cache
                .visible_structs
                .clone(),
        };

        let first_ancestor = match self {
            SubContextKind::ExternalFnCall { .. } => None,
            SubContextKind::InternalFnCall { .. } => None,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => {
                parent_ctx.underlying(analyzer)?.cache.first_ancestor
            }
            SubContextKind::FnReturn {
                continuation_of, ..
            } => continuation_of.underlying(analyzer)?.cache.first_ancestor,
        };

        Ok(ContextCache {
            visible_funcs,
            visible_structs,
            first_ancestor,
            vars: Default::default(),
            tmp_vars: Default::default(),
            storage_vars: Default::default(),
            associated_source: None,
            associated_contract: None,
        })
    }

    pub fn depth(&self, analyzer: &impl AnalyzerBackend) -> Result<usize, GraphError> {
        Ok((self.parent_ctx().underlying(analyzer)?.depth as isize)
            .saturating_add(self.self_depth())
            .max(0) as usize)
    }

    pub fn self_depth(&self) -> isize {
        match self {
            SubContextKind::ExternalFnCall { .. } => 1,
            SubContextKind::InternalFnCall { .. } => 1,
            SubContextKind::Fork { .. } => 1,
            SubContextKind::Loop { .. } => 1,
            SubContextKind::Dummy { .. } => 1,
            SubContextKind::FnReturn { .. } => -1,
        }
    }

    pub fn width(&self, analyzer: &impl AnalyzerBackend) -> Result<usize, GraphError> {
        Ok(self
            .parent_ctx()
            .underlying(analyzer)?
            .width
            .saturating_add(self.self_width()))
    }

    pub fn self_width(&self) -> usize {
        match self {
            SubContextKind::ExternalFnCall { .. } => 0,
            SubContextKind::InternalFnCall { .. } => 0,
            SubContextKind::Fork { .. } => 1,
            SubContextKind::Loop { .. } => 0,
            SubContextKind::Dummy { .. } => 0,
            SubContextKind::FnReturn { .. } => 0,
        }
    }

    pub fn continuation_of(&self) -> Option<ContextNode> {
        match self {
            SubContextKind::ExternalFnCall { .. } | SubContextKind::InternalFnCall { .. } => None,
            SubContextKind::Fork { parent_ctx, .. }
            | SubContextKind::Loop { parent_ctx }
            | SubContextKind::Dummy { parent_ctx } => Some(*parent_ctx),
            SubContextKind::FnReturn {
                continuation_of, ..
            } => Some(*continuation_of),
        }
    }

    pub fn returning_ctx(&self) -> Option<ContextNode> {
        match self {
            SubContextKind::ExternalFnCall {
                return_into_ctx, ..
            }
            | SubContextKind::InternalFnCall {
                return_into_ctx, ..
            } => Some(*return_into_ctx),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Copy)]
pub enum ContractId {
    Id(usize),
    CalledAddress(ContextVarNode),
    Dummy,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    /// The current parse index of the stack
    pub parse_idx: usize,
    /// The function associated with this context
    pub parent_fn: FunctionNode,
    /// Whether this function call is actually a modifier call
    pub modifier_state: Option<ModifierState>,

    /// The address that is being called
    pub contract_id: ContractId,

    pub subctx_kind: Option<SubContextKind>,
    /// Variables whose bounds are required to be met for this context fork to exist. i.e. a conditional operator
    /// like an if statement
    pub ctx_deps: BTreeSet<ContextVarNode>,
    /// A string that represents the path taken from the root context (i.e. `fn_entry.fork.1`)
    pub path: String,
    /// Denotes whether this context was killed by an unsatisfiable require, assert, etc. statement
    pub killed: Option<(Loc, KilledKind)>,
    /// The child context. This is either of the form `Call(child_context)` or `Fork(world1, world2)`. Once
    /// a child is defined we should *never* evaluate an expression in this context.
    pub child: Option<CallFork>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Vec<(Loc, ContextVarNode)>,
    /// Depth tracker
    pub depth: usize,
    /// Width tracker
    pub width: usize,
    /// The stack of ExprRets for this context
    pub expr_ret_stack: Vec<ExprRet>,
    /// The number of live edges
    pub number_of_live_edges: usize,
    /// Caching related things
    pub cache: ContextCache,
    /// A difference logic solver used for determining reachability
    pub dl_solver: DLSolver,
    /// Functions applied (but not reparsed) in this context
    pub applies: Vec<FunctionNode>,
    /// Current expression flag
    pub expr_flag: Option<ExprFlag>,
}

impl From<Context> for Node {
    fn from(c: Context) -> Node {
        Node::Context(c)
    }
}

impl Context {
    /// Creates a new context from a function
    pub fn new(
        parent_fn: FunctionNode,
        fn_name: String,
        loc: Loc,
        contract_id: ContractId,
    ) -> Self {
        Context {
            parse_idx: 0,
            parent_fn,
            subctx_kind: None,
            contract_id,
            path: fn_name,
            tmp_var_ctr: 0,
            killed: None,
            ctx_deps: Default::default(),
            child: None,
            ret: vec![],
            loc,
            modifier_state: None,
            depth: 0,
            width: 0,
            expr_ret_stack: Vec::with_capacity(5),
            number_of_live_edges: 0,
            cache: Default::default(),
            dl_solver: Default::default(),
            applies: Default::default(),
            expr_flag: None,
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        subctx_kind: SubContextKind,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
        modifier_state: Option<ModifierState>,
        contract_id: ContractId,
    ) -> Result<Self, GraphError> {
        let parse_idx = subctx_kind.init_parse_idx(analyzer);

        let path = format!(
            "{}.{}",
            subctx_kind.parent_ctx().path(analyzer),
            subctx_kind.path_ext(analyzer)?
        );
        let ctx_deps = subctx_kind.init_ctx_deps(analyzer)?;
        let expr_ret_stack = subctx_kind.init_expr_ret_stack(analyzer)?;
        let cache = subctx_kind.init_ctx_cache(analyzer)?;

        let depth = subctx_kind.depth(analyzer)?;

        let width = subctx_kind.width(analyzer)?;

        if analyzer.max_depth() < depth {
            return Err(GraphError::MaxStackDepthReached(format!(
                "Stack depth limit reached: {}",
                depth - 1
            )));
        }

        let tw = subctx_kind.parent_ctx().total_width(analyzer)?;
        if analyzer.max_width() < tw {
            return Err(GraphError::MaxStackWidthReached(format!(
                "Stack width limit reached: {}",
                width - 1
            )));
        }

        let parent_fn = if let Some(cont) = subctx_kind.continuation_of() {
            cont.associated_fn(analyzer)?
        } else {
            subctx_kind.parent_ctx().associated_fn(analyzer)?
        };

        let modifier_state = if let Some(mstate) = modifier_state {
            Some(mstate)
        } else if subctx_kind.fn_call().is_none() || Some(parent_fn) == subctx_kind.fn_call() {
            subctx_kind
                .parent_ctx()
                .underlying(analyzer)?
                .modifier_state
                .clone()
        } else {
            None
        };

        tracing::trace!("new subcontext path: {path}, depth: {depth}");
        Ok(Context {
            parse_idx,
            parent_fn,
            subctx_kind: Some(subctx_kind),
            contract_id,
            path,
            ctx_deps,
            expr_ret_stack,
            cache,

            tmp_var_ctr: subctx_kind.parent_ctx().underlying(analyzer)?.tmp_var_ctr,
            killed: None,
            child: None,
            ret: vec![],
            loc,
            modifier_state,
            depth,
            width,

            number_of_live_edges: 0,

            dl_solver: subctx_kind
                .parent_ctx()
                .underlying(analyzer)?
                .dl_solver
                .clone(),
            applies: Default::default(),
            expr_flag: subctx_kind.init_expr_flag(analyzer),
        })
    }

    pub fn add_subctx(
        subctx_kind: SubContextKind,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
        modifier_state: Option<ModifierState>,
        contract_id: ContractId,
    ) -> Result<ContextNode, GraphError> {
        let ctx = Context::new_subctx(subctx_kind, loc, analyzer, modifier_state, contract_id)?;
        let ctx_node = ContextNode::from(analyzer.add_node(ctx));
        if let Some(cont) = ctx_node.underlying(analyzer)?.continuation_of() {
            analyzer.add_edge(ctx_node, cont, Edge::Context(ContextEdge::Continue("TODO")));
        }
        Ok(ctx_node)
    }

    pub fn take_expr_flag(&mut self) -> Option<ExprFlag> {
        std::mem::take(&mut self.expr_flag)
    }
    pub fn set_expr_flag(&mut self, flag: ExprFlag) {
        self.expr_flag = Some(flag);
    }
    pub fn peek_expr_flag(&self) -> Option<ExprFlag> {
        self.expr_flag
    }

    pub fn add_fork_subctxs(
        analyzer: &mut impl AnalyzerBackend,
        parent_ctx: ContextNode,
        loc: Loc,
    ) -> Result<(ContextNode, ContextNode), GraphError> {
        let contract_id = parent_ctx.contract_id(analyzer)?;
        let true_subctx_kind = SubContextKind::new_fork(parent_ctx, true);
        let true_subctx = Context::add_subctx(true_subctx_kind, loc, analyzer, None, contract_id)?;

        let false_subctx_kind = SubContextKind::new_fork(parent_ctx, false);
        let false_subctx =
            Context::add_subctx(false_subctx_kind, loc, analyzer, None, contract_id)?;

        parent_ctx.set_child_fork(true_subctx, false_subctx, analyzer)?;
        let ctx_fork = analyzer.add_node(Node::ContextFork);
        analyzer.add_edge(
            ctx_fork,
            parent_ctx,
            Edge::Context(ContextEdge::ContextFork),
        );
        analyzer.add_edge(
            NodeIdx::from(true_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        analyzer.add_edge(
            NodeIdx::from(false_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        Ok((true_subctx, false_subctx))
    }

    pub fn add_loop_subctx(
        parent_ctx: ContextNode,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ContextNode, GraphError> {
        let contract_id = parent_ctx.contract_id(analyzer)?;
        let subctx_kind = SubContextKind::Loop { parent_ctx };
        let loop_ctx = Context::add_subctx(subctx_kind, loc, analyzer, None, contract_id)?;
        parent_ctx.set_child_call(loop_ctx, analyzer)?;
        analyzer.add_edge(loop_ctx, parent_ctx, Edge::Context(ContextEdge::Loop));
        Ok(loop_ctx)
    }

    /// Set the child context to a fork
    pub fn set_child_fork(&mut self, world1: ContextNode, world2: ContextNode) -> bool {
        if self.child.is_some() {
            false
        } else {
            self.child = Some(CallFork::Fork(world1, world2));
            true
        }
    }

    /// Set the child context to a call
    pub fn set_child_call(&mut self, call_ctx: ContextNode) -> bool {
        if self.child.is_some() {
            false
        } else {
            self.child = Some(CallFork::Call(call_ctx));
            true
        }
    }

    pub fn delete_child(&mut self) {
        self.child = None;
    }

    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }

    pub fn parent_ctx(&self) -> Option<ContextNode> {
        Some(self.subctx_kind?.parent_ctx())
    }

    pub fn fn_call(&self) -> Option<FunctionNode> {
        self.subctx_kind?.fn_call()
    }

    pub fn continuation_of(&self) -> Option<ContextNode> {
        self.subctx_kind?.continuation_of()
    }

    pub fn returning_ctx(&self) -> Option<ContextNode> {
        self.subctx_kind?.returning_ctx()
    }

    pub fn is_ext_fn_call(&self) -> bool {
        matches!(
            self.subctx_kind,
            Some(SubContextKind::ExternalFnCall { .. })
        )
    }
}
