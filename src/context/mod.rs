use crate::range::ElemEval;
use crate::range::RangeSize;
use crate::VarType;
use crate::{
    range::{DynamicRangeSide, Op, RangeElem},
    AnalyzerLike, Builtin, Edge, FunctionNode, FunctionParamNode, FunctionReturnNode, Node,
    NodeIdx,
};
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{Expression, Loc, Statement};
use std::collections::HashMap;

pub mod var;
pub use var::*;
pub mod exprs;
use exprs::*;

pub mod analyzers;
pub use analyzers::*;

#[derive(Debug, Clone)]
pub enum ExprRet {
    CtxKilled,
    Single((ContextNode, NodeIdx)),
    Multi(Vec<ExprRet>),
    Fork(Box<ExprRet>, Box<ExprRet>),
}

impl ExprRet {
    pub fn expect_single(&self) -> (ContextNode, NodeIdx) {
        match self {
            ExprRet::Single(inner) => *inner,
            _ => panic!("Expected a single return got multiple"),
        }
    }

    pub fn expect_multi(self) -> Vec<ExprRet> {
        match self {
            ExprRet::Multi(inner) => inner,
            _ => panic!("Expected a multi return got single"),
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

    // Variable incoming edges
    Assign,
    StorageAssign,
    MemoryAssign,
    Prev,

    // Control flow
    Return,

    // Range analysis
    Range,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);
impl ContextNode {
    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl AnalyzerLike) -> String {
        self.underlying(analyzer).path.clone()
    }

    /// *All* subcontexts (including subcontexts of subcontexts, recursively)
    pub fn subcontexts(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<ContextNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Subcontext))
            .into_iter()
            .map(|idx| ContextNode::from(idx))
            .collect()
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &(impl AnalyzerLike + Search)) -> FunctionNode {
        self.underlying(analyzer).parent_fn
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        self.underlying(analyzer).parent_fn.name(analyzer)
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl AnalyzerLike) -> &'a mut Context {
        match analyzer.node_mut(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Context {
        match analyzer.node(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    /// Gets a variable by name in the context
    pub fn var_by_name(&self, analyzer: &impl AnalyzerLike, name: &str) -> Option<ContextVarNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
            .into_iter()
            .filter_map(|cvar_node| {
                let cvar_node = ContextVarNode::from(cvar_node);
                let cvar = cvar_node.underlying(analyzer);
                if cvar.name == name {
                    Some(cvar_node)
                } else {
                    None
                }
            })
            .take(1)
            .next()
    }

    /// Gets all variables associated with a context
    pub fn vars(&self, analyzer: &impl AnalyzerLike) -> Vec<ContextVarNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
            .into_iter()
            .map(|idx| ContextVarNode::from(idx))
            .collect()
    }

    /// Gets the latest version of a variable associated with a context
    pub fn latest_var_by_name(
        &self,
        analyzer: &impl AnalyzerLike,
        name: &str,
    ) -> Option<ContextVarNode> {
        if let Some(var) = self.var_by_name(analyzer, name) {
            Some(var.latest_version(analyzer))
        } else {
            None
        }
    }

    /// Reads the current temporary counter and increments the counter
    pub fn new_tmp(&self, analyzer: &mut impl AnalyzerLike) -> usize {
        let context = self.underlying_mut(analyzer);
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        ret
    }

    /// Returns all forks associated with the context
    pub fn forks(&self, analyzer: &impl AnalyzerLike) -> Vec<Self> {
        let context = self.underlying(analyzer);
        context.forks.clone()
    }

    /// Returns all *live* forks associated with the context
    pub fn live_forks(&self, analyzer: &impl AnalyzerLike) -> Vec<Self> {
        let context = self.underlying(analyzer);
        context
            .forks
            .iter()
            .filter(|fork_ctx| !fork_ctx.is_killed(analyzer))
            .cloned()
            .collect()
    }

    /// Adds a fork to the context
    pub fn add_fork(&self, fork: ContextNode, analyzer: &mut impl AnalyzerLike) {
        let context = self.underlying_mut(analyzer);
        context.add_fork(fork);
    }

    /// Kills the context by denoting it as killed. Recurses up the contexts and kills
    /// parent contexts if all subcontexts of that context are killed
    pub fn kill(&self, analyzer: &mut impl AnalyzerLike, kill_loc: Loc) {
        let context = self.underlying_mut(analyzer);
        context.killed = Some(kill_loc);
        if let Some(parent_ctx) = context.parent_ctx {
            parent_ctx.kill_if_all_forks_killed(analyzer, kill_loc);
        }
    }

    /// Kills if and only if all subcontexts are killed
    pub fn kill_if_all_forks_killed(&self, analyzer: &mut impl AnalyzerLike, kill_loc: Loc) {
        let context = self.underlying(analyzer);
        if context
            .forks
            .iter()
            .all(|fork_ctx| fork_ctx.is_killed(analyzer))
        {
            let context = self.underlying_mut(analyzer);
            context.killed = Some(kill_loc);
            if let Some(parent_ctx) = context.parent_ctx {
                parent_ctx.kill_if_all_forks_killed(analyzer, kill_loc);
            }
        }
    }

    /// Returns whether the context is killed
    pub fn is_killed(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).killed.is_some()
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(&self, analyzer: &impl AnalyzerLike) -> Option<Loc> {
        self.underlying(analyzer).killed
    }

    /// Returns a vector of variable dependencies for this context
    pub fn ctx_deps(&self, analyzer: &impl AnalyzerLike) -> HashMap<String, ContextVarNode> {
        self.underlying(analyzer).ctx_deps.clone()
    }

    /// Returns a vector of variable dependencies for this context
    pub fn add_ctx_dep(&self, dep: ContextVarNode, analyzer: &mut impl AnalyzerLike) {
        if !dep.is_const(analyzer) {
            let dep_name = dep.name(analyzer);
            let underlying = self.underlying_mut(analyzer);
            underlying.ctx_deps.insert(dep_name, dep);
        }
    }

    pub fn set_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut impl AnalyzerLike,
    ) {
        self.underlying_mut(analyzer).ret = Some((ret_stmt_loc, ret));
    }

    pub fn return_node(&self, analyzer: &impl AnalyzerLike) -> Option<(Loc, ContextVarNode)> {
        self.underlying(analyzer).ret
    }
}

impl Into<NodeIdx> for ContextNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    /// The function associated with this context
    pub parent_fn: FunctionNode,
    /// An optional parent context (i.e. this context is a fork or subcontext of another previous context)
    pub parent_ctx: Option<ContextNode>,
    /// Variables whose bounds are required to be met for this context fork to exist. i.e. a conditional operator
    /// like an if statement
    pub ctx_deps: HashMap<String, ContextVarNode>,
    /// A string that represents the path taken from the root context (i.e. `fn_entry.fork.1`)
    pub path: String,
    /// Denotes whether this context was killed by an unsatisfiable require, assert, etc. statement
    pub killed: Option<Loc>,
    /// Denotes whether this context is a fork of another context
    pub is_fork: bool,
    /// A vector of forks of this context
    pub forks: Vec<ContextNode>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Option<(Loc, ContextVarNode)>,
}

impl Context {
    /// Creates a new context from a function
    pub fn new(parent_fn: FunctionNode, fn_name: String, loc: Loc) -> Self {
        Context {
            parent_fn,
            parent_ctx: None,
            path: fn_name,
            tmp_var_ctr: 0,
            killed: None,
            ctx_deps: Default::default(),
            is_fork: false,
            forks: vec![],
            ret: None,
            loc,
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        parent_ctx: ContextNode,
        loc: Loc,
        is_fork: bool,
        analyzer: &impl AnalyzerLike,
    ) -> Self {
        Context {
            parent_fn: parent_ctx.underlying(analyzer).parent_fn.clone(),
            parent_ctx: Some(parent_ctx),
            path: format!(
                "{}.{}",
                parent_ctx.underlying(analyzer).path,
                if is_fork {
                    format!("fork.{}", parent_ctx.underlying(analyzer).forks.len())
                } else {
                    "child".to_string()
                }
            ),
            is_fork,
            ctx_deps: parent_ctx.underlying(analyzer).ctx_deps.clone(),
            killed: None,
            forks: vec![],
            tmp_var_ctr: 0,
            ret: None,
            loc,
        }
    }

    /// Add a fork to this context
    pub fn add_fork(&mut self, fork_node: ContextNode) {
        self.forks.push(fork_node);
    }
}

impl<T> ContextBuilder for T where T: AnalyzerLike + Sized + ExprParser {}

pub trait ContextBuilder: AnalyzerLike + Sized + ExprParser {
    fn parse_ctx_statement(
        &mut self,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        println!("stmt: {:?}\n", stmt);
        if let Some(parent) = parent_ctx {
            match self.node(parent) {
                Node::Context(_) => {
                    let ctx = ContextNode::from(parent.into());
                    if ctx.is_killed(self) {
                        return;
                    }
                    if ctx.live_forks(self).is_empty() {
                        self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
                    } else {
                        ctx.live_forks(self).iter().for_each(|fork_ctx| {
                            self.parse_ctx_stmt_inner(stmt, unchecked, Some(*fork_ctx));
                        });
                    }
                }
                _ => self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx),
            }
        } else {
            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
        }
    }

    fn parse_ctx_stmt_inner(
        &mut self,
        stmt: &Statement,
        _unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        use Statement::*;
        match stmt {
            Block {
                loc,
                unchecked,
                statements,
            } => {
                let parent = parent_ctx.expect("Free floating contexts shouldn't happen");
                let ctx_node = match self.node(parent) {
                    Node::Function(_fn_node) => {
                        let ctx = Context::new(
                            FunctionNode::from(parent.into()),
                            FunctionNode::from(parent.into()).name(self),
                            *loc,
                        );
                        let ctx_node = self.add_node(Node::Context(ctx));
                        self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Context));
                        ctx_node
                    }
                    Node::Context(_) => {
                        // let ctx = Context::new_subctx(
                        //     ContextNode::from(parent.into()),
                        //     *loc,
                        //     false,
                        //     self,
                        // );
                        // let ctx_node = self.add_node(Node::Context(ctx));
                        // self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Subcontext));
                        // ctx_node
                        parent.into()
                    }
                    e => todo!(
                        "Expected a context to be created by a function or context but got: {:?}",
                        e
                    ),
                };

                // optionally add named input and named outputs into context
                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionParam)
                    .map(|edge| FunctionParamNode::from(edge.source()))
                    .collect::<Vec<FunctionParamNode>>()
                    .iter()
                    .for_each(|param_node| {
                        let func_param = param_node.underlying(self);
                        if let Some(cvar) =
                            ContextVar::maybe_new_from_func_param(self, func_param.clone())
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionReturn)
                    .map(|edge| FunctionReturnNode::from(edge.source()))
                    .collect::<Vec<FunctionReturnNode>>()
                    .iter()
                    .for_each(|ret_node| {
                        let func_ret = ret_node.underlying(self);
                        if let Some(cvar) =
                            ContextVar::maybe_new_from_func_ret(self, func_ret.clone())
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                let forks = ContextNode::from(ctx_node).live_forks(self);
                if forks.is_empty() {
                    statements.iter().for_each(|stmt| {
                        self.parse_ctx_statement(stmt, *unchecked, Some(ctx_node))
                    });
                } else {
                    forks.into_iter().for_each(|fork| {
                        statements.iter().for_each(|stmt| {
                            self.parse_ctx_statement(stmt, *unchecked, Some(fork))
                        });
                    });
                }
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                let forks = ctx.live_forks(self);
                if forks.is_empty() {
                    let name = var_decl.name.clone().expect("Variable wasn't named");
                    let (lhs_ctx, ty) = self.parse_ctx_expr(&var_decl.ty, ctx).expect_single();
                    let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                    let var = ContextVar {
                        loc: Some(*loc),
                        name: name.to_string(),
                        display_name: name.to_string(),
                        storage: var_decl.storage.clone(),
                        is_tmp: false,
                        tmp_of: None,
                        ty,
                    };
                    if let Some(rhs) = maybe_expr {
                        let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                        self.match_var_def(*loc, &var, &rhs_paths);
                    } else {
                        let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                        self.add_edge(lhs, lhs_ctx, Edge::Context(ContextEdge::Variable));
                    }
                } else {
                    forks.into_iter().for_each(|ctx| {
                        let name = var_decl.name.clone().expect("Variable wasn't named");
                        let (lhs_ctx, ty) = self.parse_ctx_expr(&var_decl.ty, ctx).expect_single();
                        let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                        let var = ContextVar {
                            loc: Some(*loc),
                            name: name.to_string(),
                            display_name: name.to_string(),
                            storage: var_decl.storage.clone(),
                            is_tmp: false,
                            tmp_of: None,
                            ty,
                        };
                        if let Some(rhs) = maybe_expr {
                            let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                            self.match_var_def(*loc, &var, &rhs_paths);
                        } else {
                            let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                            self.add_edge(lhs, lhs_ctx, Edge::Context(ContextEdge::Variable));
                        }
                    });
                }
            }
            Assembly {
                loc: _,
                dialect: _,
                flags: _,
                block: _yul_block,
            } => {}
            Args(_loc, _args) => {}
            If(loc, if_expr, true_expr, maybe_false_expr) => {
                let ctx = ContextNode::from(parent_ctx.expect("Dangling if statement").into());
                let forks = ctx.live_forks(self);
                if forks.is_empty() {
                    self.cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, ctx)
                } else {
                    forks.into_iter().for_each(|parent| {
                        self.cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, parent.into())
                    })
                }
            }
            While(_loc, _cond, _body) => {}
            Expression(_loc, expr) => {
                if let Some(parent) = parent_ctx {
                    let _paths = self.parse_ctx_expr(expr, ContextNode::from(parent.into()));
                }
            }
            For(_loc, _maybe_for_start, _maybe_for_middle, _maybe_for_end, _maybe_for_body) => {}
            DoWhile(_loc, _while_stmt, _while_expr) => {}
            Continue(_loc) => {}
            Break(_loc) => {}
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let forks = ContextNode::from(parent.into()).live_forks(self);
                        if forks.is_empty() {
                            let paths =
                                self.parse_ctx_expr(ret_expr, ContextNode::from(parent.into()));
                            println!("return paths: {:?}", paths);
                            match paths {
                                ExprRet::CtxKilled => {}
                                ExprRet::Single((ctx, expr)) => {
                                    println!("adding return: {:?}", ctx.path(self));
                                    self.add_edge(expr, ctx, Edge::Context(ContextEdge::Return));
                                    ctx.set_return_node(*loc, expr.into(), self);
                                }
                                ExprRet::Multi(rets) => {
                                    rets.into_iter().for_each(|expr_ret| {
                                        let (ctx, expr) = expr_ret.expect_single();
                                        self.add_edge(
                                            expr,
                                            ctx,
                                            Edge::Context(ContextEdge::Return),
                                        );
                                        ctx.set_return_node(*loc, expr.into(), self);
                                    });
                                }
                                ExprRet::Fork(_world1, _world2) => {
                                    todo!("here")
                                }
                            }
                        } else {
                            forks.into_iter().for_each(|parent| {
                                let paths =
                                    self.parse_ctx_expr(ret_expr, ContextNode::from(parent));
                                match paths {
                                    ExprRet::CtxKilled => {}
                                    ExprRet::Single((ctx, expr)) => {
                                        self.add_edge(
                                            expr,
                                            ctx,
                                            Edge::Context(ContextEdge::Return),
                                        );
                                        ctx.set_return_node(*loc, expr.into(), self);
                                    }
                                    ExprRet::Multi(rets) => {
                                        rets.into_iter().for_each(|expr_ret| {
                                            let (ctx, expr) = expr_ret.expect_single();
                                            self.add_edge(
                                                expr,
                                                ctx,
                                                Edge::Context(ContextEdge::Return),
                                            );
                                            ctx.set_return_node(*loc, expr.into(), self);
                                        });
                                    }
                                    ExprRet::Fork(_world1, _world2) => {
                                        todo!("here")
                                    }
                                }
                            });
                        }
                    }
                }
            }
            Revert(loc, _maybe_err_path, _exprs) => {
                if let Some(parent) = parent_ctx {
                    let parent = ContextNode::from(parent.into());
                    let forks = parent.live_forks(self);
                    if forks.is_empty() {
                        parent.kill(self, *loc);
                    } else {
                        forks.into_iter().for_each(|parent| {
                            parent.kill(self, *loc);
                        });
                    }
                }
            }
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {}
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }

    fn match_var_def(&mut self, loc: Loc, var: &ContextVar, rhs_paths: &ExprRet) {
        match rhs_paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((rhs_ctx, rhs)) => {
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var.clone())));
                self.add_edge(lhs, *rhs_ctx, Edge::Context(ContextEdge::Variable));
                let rhs = ContextVarNode::from(*rhs);
                let (_, new_lhs) = self.assign(loc, lhs, rhs, *rhs_ctx).expect_single();
                self.add_edge(new_lhs, *rhs_ctx, Edge::Context(ContextEdge::Variable));
            }
            ExprRet::Multi(rets) => {
                rets.into_iter().for_each(|expr_ret| {
                    self.match_var_def(loc, var, expr_ret);
                });
            }
            ExprRet::Fork(world1, world2) => {
                self.match_var_def(loc, var, world1);
                self.match_var_def(loc, var, world2);
            }
        }
    }

    fn match_expr(&mut self, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) => {
                self.add_edge(*expr, *ctx, Edge::Context(ContextEdge::Call));
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    self.match_expr(expr_ret);
                });
            }
            ExprRet::Fork(world1, world2) => {
                self.match_expr(world1);
                self.match_expr(world2);
            }
        }
    }

    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> ExprRet {
        if ctx.is_killed(self) {
            return ExprRet::CtxKilled;
        }

        println!("has any forks: {}", ctx.forks(self).len());
        if ctx.live_forks(self).is_empty() {
            println!("has no live forks");
            self.parse_ctx_expr_inner(expr, ctx)
        } else {
            println!("has live forks");
            ctx.live_forks(self).iter().for_each(|fork_ctx| {
                // println!("fork_ctx: {}\n", fork_ctx.underlying(self).path);
                self.parse_ctx_expr_inner(expr, *fork_ctx);
            });
            ExprRet::Multi(vec![])
        }
    }

    fn parse_ctx_expr_inner(&mut self, expr: &Expression, ctx: ContextNode) -> ExprRet {
        use Expression::*;
        println!("ctx: {}, {:?}\n", ctx.underlying(self).path, expr);
        match expr {
            Variable(ident) => self.variable(ident, ctx),
            // literals
            NumberLiteral(loc, int, exp) => self.number_literal(ctx, *loc, int, exp),
            AddressLiteral(loc, addr) => self.address_literal(ctx, *loc, addr),
            StringLiteral(lits) => ExprRet::Multi(
                lits.iter()
                    .map(|lit| self.string_literal(ctx, lit.loc, &lit.string))
                    .collect(),
            ),
            BoolLiteral(loc, b) => self.bool_literal(ctx, *loc, *b),
            // bin ops
            Add(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Add, false)
            }
            AssignAdd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Add, true)
            }
            Subtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Sub, false)
            }
            AssignSubtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Sub, true)
            }
            Multiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mul, false)
            }
            AssignMultiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mul, true)
            }
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Div, false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Div, true)
            }
            Modulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mod, false)
            }
            AssignModulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mod, true)
            }
            ShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Shl, false)
            }
            AssignShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Shl, true)
            }
            ShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Shr, false)
            }
            AssignShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Shr, true)
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {
                self.cond_op_expr(*loc, if_expr, true_expr, false_expr, ctx)
            }
            // assign
            Assign(loc, lhs_expr, rhs_expr) => self.assign_exprs(*loc, lhs_expr, rhs_expr, ctx),
            List(loc, params) => self.list(ctx, *loc, params),
            // array
            ArraySubscript(_loc, ty_expr, None) => self.array_ty(ty_expr, ctx),
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.index_into_array(*loc, ty_expr, index_expr, ctx)
            }
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone()) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        ExprRet::Single((ctx, *idx))
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        ExprRet::Single((ctx, idx))
                    }
                } else {
                    todo!("??")
                }
            }
            MemberAccess(loc, member_expr, ident) => {
                self.member_access(*loc, member_expr, ident, ctx)
            }
            // // comparator
            Equal(loc, lhs, rhs) => self.cmp(*loc, lhs, Op::Eq, rhs, ctx),
            Less(loc, lhs, rhs) => self.cmp(*loc, lhs, Op::Lt, rhs, ctx),
            More(loc, lhs, rhs) => self.cmp(*loc, lhs, Op::Gt, rhs, ctx),
            LessEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, Op::Lte, rhs, ctx),
            MoreEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, Op::Gte, rhs, ctx),

            Not(loc, expr) => self.not(*loc, expr, ctx),
            FunctionCall(loc, func_expr, input_exprs) => {
                let (_ctx, func_idx) = self.parse_ctx_expr(func_expr, ctx).expect_single();
                match self.node(func_idx) {
                    Node::Function(underlying) => {
                        if let Some(func_name) = &underlying.name {
                            match &*func_name.name {
                                "require" | "assert" => {
                                    self.handle_require(input_exprs, ctx);
                                    return ExprRet::Multi(vec![]);
                                }
                                _ => {}
                            }
                        }
                    }
                    Node::Builtin(_ty) => {
                        // it is a cast
                        let (ctx, cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();

                        let new_var = self.advance_var_in_ctx(cvar.into(), *loc, ctx);
                        new_var.underlying_mut(self).ty =
                            VarType::try_from_idx(self, func_idx).expect("");
                        if let Some(r) = ContextVarNode::from(cvar).range(self) {
                            // TODO: cast the ranges appropriately (set cap or convert to signed/unsigned concrete)
                            new_var.set_range_min(self, r.range_min());
                            new_var.set_range_max(self, r.range_max());
                        }
                        return ExprRet::Single((ctx, new_var.into()));
                    }
                    _ => todo!(),
                }

                let _inputs: Vec<_> = input_exprs
                    .into_iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                // todo!("func call")
                // vec![func_idx]
                ExprRet::Single((ctx, func_idx))
            }

            e => todo!("{:?}", e),
        }
    }

    fn assign_exprs(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(&lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(&rhs_expr, ctx);
        self.match_assign_sides(loc, &lhs_paths, &rhs_paths, ctx)
    }

    fn match_assign_sides(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        ctx: ContextNode,
    ) -> ExprRet {
        match (lhs_paths, rhs_paths) {
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                self.assign(loc, lhs_cvar, rhs_cvar, *rhs_ctx)
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => ExprRet::Multi(
                rhs_sides
                    .iter()
                    .map(|expr_ret| self.match_assign_sides(loc, l, expr_ret, ctx))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => ExprRet::Multi(
                lhs_sides
                    .iter()
                    .map(|expr_ret| self.match_assign_sides(loc, expr_ret, r, ctx))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    ExprRet::Multi(
                        lhs_sides
                            .iter()
                            .zip(rhs_sides.iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.match_assign_sides(loc, lhs_expr_ret, rhs_expr_ret, ctx)
                            })
                            .collect(),
                    )
                } else {
                    ExprRet::Multi(
                        rhs_sides
                            .iter()
                            .map(|rhs_expr_ret| {
                                self.match_assign_sides(loc, lhs_paths, rhs_expr_ret, ctx)
                            })
                            .collect(),
                    )
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                ExprRet::Fork(
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world1, ctx)),
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world2, ctx)),
                    )),
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world1, ctx)),
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world2, ctx)),
                    )),
                )
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, l, world1, ctx)),
                Box::new(self.match_assign_sides(loc, l, world2, ctx)),
            ),
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, m, world1, ctx)),
                Box::new(self.match_assign_sides(loc, m, world2, ctx)),
            ),
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    fn assign(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> ExprRet {
        let (new_lower_bound, new_upper_bound) = if let Some(range) = rhs_cvar.range(self) {
            (range.range_min(), range.range_max())
        } else {
            if let Some(range) = lhs_cvar.range(self) {
                (
                    range.elem_from_dyn(rhs_cvar.into(), DynamicRangeSide::Min, loc),
                    range.elem_from_dyn(rhs_cvar.into(), DynamicRangeSide::Max, loc),
                )
            } else {
                panic!("in assign, both lhs and rhs had no range")
            }
        };

        let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx);
        new_lhs.set_range_min(self, new_lower_bound.into());
        new_lhs.set_range_max(self, new_upper_bound.into());

        ExprRet::Single((ctx, new_lhs.into()))
    }

    fn advance_var_in_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> ContextVarNode {
        // println!("advancing: {}", cvar_node.display_name(self));
        let mut new_cvar = cvar_node.underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
            if old_ctx != ctx {
                self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
            } else {
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        } else {
            self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        }

        ContextVarNode::from(new_cvarnode)
    }

    fn advance_var_underlying(&mut self, cvar_node: ContextVarNode, loc: Loc) -> &mut ContextVar {
        let mut new_cvar = cvar_node.underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode).underlying_mut(self)
    }
}
