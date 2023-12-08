use crate::{
    nodes::{
        CallFork, ContextCache, ContextNode, ContextVarNode, ExprRet, FunctionNode, KilledKind,
        ModifierState,
    },
    solvers::dl::DLSolver,
    AnalyzerBackend, GraphError,
};

use solang_parser::pt::Loc;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    /// The function associated with this context
    pub parent_fn: FunctionNode,
    /// Whether this function call is actually a modifier call
    pub modifier_state: Option<ModifierState>,
    /// An optional parent context (i.e. this context is a fork or subcontext of another previous context)
    pub parent_ctx: Option<ContextNode>,
    pub returning_ctx: Option<ContextNode>,
    /// Variables whose bounds are required to be met for this context fork to exist. i.e. a conditional operator
    /// like an if statement
    pub ctx_deps: Vec<ContextVarNode>,
    /// A string that represents the path taken from the root context (i.e. `fn_entry.fork.1`)
    pub path: String,
    /// Denotes whether this context was killed by an unsatisfiable require, assert, etc. statement
    pub killed: Option<(Loc, KilledKind)>,
    /// Denotes whether this context is a fork of another context
    pub is_fork: bool,
    /// Denotes whether this context is the result of a internal function call, and points to the FunctionNode
    pub fn_call: Option<FunctionNode>,
    /// Denotes whether this context is the result of a internal function call, and points to the FunctionNode
    pub ext_fn_call: Option<FunctionNode>,
    /// The child context. This is either of the form `Call(child_context)` or `Fork(world1, world2)`. Once
    /// a child is defined we should *never* evaluate an expression in this context.
    pub child: Option<CallFork>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Vec<(Loc, Option<ContextVarNode>)>,
    /// Depth tracker
    pub depth: usize,
    /// Width tracker
    pub width: usize,
    /// A temporary stack of ExprRets for this context
    pub tmp_expr: Vec<Option<ExprRet>>,
    /// The stack of ExprRets for this context
    pub expr_ret_stack: Vec<ExprRet>,
    /// Whether the context currently uses unchecked math
    pub unchecked: bool,
    /// The number of live edges
    pub number_of_live_edges: usize,
    /// Caching related things
    pub cache: ContextCache,
    /// A difference logic solver used for determining reachability
    pub dl_solver: DLSolver,
}

impl Context {
    /// Creates a new context from a function
    pub fn new(parent_fn: FunctionNode, fn_name: String, loc: Loc) -> Self {
        Context {
            parent_fn,
            parent_ctx: None,
            returning_ctx: None,
            path: fn_name,
            tmp_var_ctr: 0,
            killed: None,
            ctx_deps: Default::default(),
            is_fork: false,
            fn_call: None,
            ext_fn_call: None,
            child: None,
            ret: vec![],
            loc,
            modifier_state: None,
            depth: 0,
            width: 0,
            expr_ret_stack: Vec::with_capacity(5),
            tmp_expr: vec![],
            unchecked: false,
            number_of_live_edges: 0,
            cache: Default::default(),
            dl_solver: Default::default(),
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        parent_ctx: ContextNode,
        returning_ctx: Option<ContextNode>,
        loc: Loc,
        fork_expr: Option<&str>,
        fn_call: Option<FunctionNode>,
        fn_ext: bool,
        analyzer: &mut impl AnalyzerBackend,
        modifier_state: Option<ModifierState>,
    ) -> Result<Self, GraphError> {
        let mut depth =
            parent_ctx.underlying(analyzer)?.depth + if fork_expr.is_some() { 0 } else { 1 };

        let width =
            parent_ctx.underlying(analyzer)?.width + if fork_expr.is_some() { 1 } else { 0 };

        let modifier_state = if let Some(mstate) = modifier_state {
            Some(mstate)
        } else {
            parent_ctx.underlying(analyzer)?.modifier_state.clone()
        };

        if analyzer.max_depth() < depth {
            return Err(GraphError::MaxStackDepthReached(format!(
                "Stack depth limit reached: {}",
                depth - 1
            )));
        }

        let tw = parent_ctx.total_width(analyzer)?;
        if analyzer.max_width() < tw {
            return Err(GraphError::MaxStackWidthReached(format!(
                "Stack width limit reached: {}",
                width - 1
            )));
        }

        let (fn_name, ext_fn_call, fn_call) = if let Some(fn_call) = fn_call {
            if fn_ext {
                (fn_call.name(analyzer)?, Some(fn_call), None)
            } else {
                (fn_call.name(analyzer)?, None, Some(fn_call))
            }
        } else if let Some(returning_ctx) = returning_ctx {
            let fn_node = returning_ctx.associated_fn(analyzer)?;
            (fn_node.name(analyzer)?, None, Some(fn_node))
        } else {
            ("anonymous_fn_call".to_string(), None, None)
        };

        let path = format!(
            "{}.{}",
            parent_ctx.underlying(analyzer)?.path,
            if let Some(ref fork_expr) = fork_expr {
                format!("fork{{ {} }}", fork_expr)
            } else if let Some(returning_ctx) = returning_ctx {
                depth = depth.saturating_sub(2);
                format!(
                    "resume{{ {} }}",
                    returning_ctx.associated_fn_name(analyzer)?
                )
            } else {
                fn_name
            }
        );

        let parent_fn = parent_ctx.associated_fn(analyzer)?;

        parent_ctx.underlying_mut(analyzer)?.number_of_live_edges += 1;

        tracing::trace!("new subcontext path: {path}, depth: {depth}");
        Ok(Context {
            parent_fn,
            parent_ctx: Some(parent_ctx),
            returning_ctx,
            path,
            is_fork: fork_expr.is_some(),
            fn_call,
            ext_fn_call,
            ctx_deps: parent_ctx.underlying(analyzer)?.ctx_deps.clone(),
            killed: None,
            child: None,
            tmp_var_ctr: parent_ctx.underlying(analyzer)?.tmp_var_ctr,
            ret: vec![],
            loc,
            modifier_state,
            depth,
            width,
            expr_ret_stack: if fork_expr.is_some() {
                parent_ctx.underlying(analyzer)?.expr_ret_stack.clone()
            } else if let Some(ret_ctx) = returning_ctx {
                ret_ctx.underlying(analyzer)?.expr_ret_stack.clone()
            } else {
                vec![]
            },
            tmp_expr: if fork_expr.is_some() {
                parent_ctx.underlying(analyzer)?.tmp_expr.clone()
            } else if let Some(ret_ctx) = returning_ctx {
                ret_ctx.underlying(analyzer)?.tmp_expr.clone()
            } else {
                vec![]
            },
            unchecked: if fork_expr.is_some() {
                parent_ctx.underlying(analyzer)?.unchecked
            } else if let Some(ret_ctx) = returning_ctx {
                ret_ctx.underlying(analyzer)?.unchecked
            } else {
                false
            },
            number_of_live_edges: 0,
            cache: ContextCache {
                vars: Default::default(),
                visible_funcs: if fork_expr.is_some() {
                    parent_ctx.underlying(analyzer)?.cache.visible_funcs.clone()
                } else if let Some(ret_ctx) = returning_ctx {
                    ret_ctx.underlying(analyzer)?.cache.visible_funcs.clone()
                } else {
                    None
                },
                first_ancestor: if fork_expr.is_some() {
                    parent_ctx.underlying(analyzer)?.cache.first_ancestor
                } else if let Some(ret_ctx) = returning_ctx {
                    ret_ctx.underlying(analyzer)?.cache.first_ancestor
                } else {
                    None
                },
                associated_source: None,
                associated_contract: None,
            },
            dl_solver: parent_ctx.underlying(analyzer)?.dl_solver.clone(),
        })
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
}
