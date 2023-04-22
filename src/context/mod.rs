use crate::context::yul::YulBuilder;
use ethers_core::types::U256;
use shared::analyzer::AsDotStr;
use shared::analyzer::GraphLike;
use shared::context::*;
use solang_parser::helpers::CodeLocation;
use solang_parser::pt::YulStatement;

use shared::range::elem_ty::Dynamic;

use shared::range::elem_ty::Elem;
use shared::range::Range;
use solang_parser::pt::VariableDeclaration;

use crate::VarType;
use petgraph::{visit::EdgeRef, Direction};
use shared::{analyzer::AnalyzerLike, nodes::*, range::elem::RangeOp, Edge, Node, NodeIdx};
use solang_parser::pt::{Expression, Loc, Statement};

// pub mod func;
// use func::*;
pub mod func_call;
use func_call::*;

pub mod loops;
use loops::*;

pub mod exprs;
use exprs::*;

pub mod analyzers;
pub mod queries;

pub mod yul;

#[derive(Debug, Clone)]
pub enum ExprRet {
    CtxKilled,
    Single((ContextNode, NodeIdx)),
    SingleLiteral((ContextNode, NodeIdx)),
    Multi(Vec<ExprRet>),
    Fork(Box<ExprRet>, Box<ExprRet>),
}

impl ExprRet {
    pub fn debug_str(&self, analyzer: &impl GraphLike) -> String {
        match self {
            ExprRet::Single((_, inner)) | ExprRet::SingleLiteral((_, inner)) => {
                match analyzer.node(*inner) {
                    Node::ContextVar(_) => {
                        ContextVarNode::from(*inner).display_name(analyzer).unwrap()
                    }
                    e => format!("{:?}", e),
                }
            }
            ExprRet::Multi(inner) => {
                format!(
                    "[{}]",
                    inner
                        .iter()
                        .map(|i| i.debug_str(analyzer))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ExprRet::Fork(w1, w2) => {
                format!("({} || {})", w1.debug_str(analyzer), w2.debug_str(analyzer))
            }
            ExprRet::CtxKilled => "CtxKilled".to_string(),
        }
    }

    pub fn expect_single(&self, loc: Loc) -> Result<(ContextNode, NodeIdx), ExprErr> {
        match self {
            ExprRet::Single(inner) => Ok(*inner),
            ExprRet::SingleLiteral(inner) => Ok(*inner),
            ExprRet::Multi(inner) if inner.len() == 1 => Ok(inner[0].expect_single(loc)?),
            e => Err(ExprErr::ExpectedSingle(
                loc,
                format!("Expected a single return got: {e:?}"),
            )),
        }
    }

    pub fn is_single(&self) -> bool {
        match self {
            ExprRet::Single(_inner) => true,
            ExprRet::SingleLiteral(_inner) => true,
            ExprRet::Multi(inner) => inner.len() == 1,
            _ => false,
        }
    }

    pub fn is_killed(&self) -> bool {
        matches!(self, ExprRet::CtxKilled)
    }

    pub fn has_killed(&self) -> bool {
        match self {
            ExprRet::CtxKilled => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_killed()),
            ExprRet::Fork(w1, w2) => w1.has_killed() && w2.has_killed(),
            _ => false,
        }
    }

    pub fn has_fork(&self) -> bool {
        match self {
            ExprRet::Fork(_, _) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_fork()),
            _ => false,
        }
    }

    pub fn has_literal(&self) -> bool {
        match self {
            ExprRet::SingleLiteral(..) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_literal()),
            _ => false,
        }
    }

    pub fn expect_multi(self) -> Vec<ExprRet> {
        match self {
            ExprRet::Multi(inner) => inner,
            _ => panic!("Expected a multi return got single"),
        }
    }

    pub fn try_as_func_input_str(&self, analyzer: &impl GraphLike) -> String {
        match self {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => {
                let (_, idx) = inner;
                match VarType::try_from_idx(analyzer, *idx) {
                    Some(var_ty) => format!("({})", var_ty.as_dot_str(analyzer)),
                    None => "UnresolvedType".to_string(),
                }
            }
            ExprRet::Multi(inner) if !self.has_fork() => {
                let mut strs = vec![];
                for ret in inner.iter() {
                    strs.push(ret.try_as_func_input_str(analyzer).replace(['(', ')'], ""));
                }
                format!("({})", strs.join(", "))
            }
            e => todo!("here: {e:?}"),
        }
    }

    pub fn as_flat_vec(&self) -> Vec<NodeIdx> {
        let mut idxs = vec![];
        match self {
            ExprRet::Single((_, idx)) | ExprRet::SingleLiteral((_, idx)) => idxs.push(*idx),
            ExprRet::Multi(inner) => {
                idxs.extend(
                    inner
                        .iter()
                        .flat_map(|expr| expr.as_flat_vec())
                        .collect::<Vec<_>>(),
                );
            }
            _ => {}
        }
        idxs
    }

    pub fn flatten(self) -> Self {
        match self {
            ExprRet::Single((_, _)) | ExprRet::SingleLiteral((_, _)) => self,
            ExprRet::Multi(inner) => {
                if inner.len() == 1 {
                    inner[0].to_owned().flatten()
                } else {
                    ExprRet::Multi(inner.into_iter().map(|i| i.flatten()).collect())
                }
            }
            ExprRet::Fork(lhs, rhs) => match (&*lhs, &*rhs) {
                (ExprRet::Multi(lhs_inner), ExprRet::Multi(rhs_inner)) => {
                    match (lhs_inner.is_empty(), rhs_inner.is_empty()) {
                        (true, true) => ExprRet::Multi(vec![]),
                        (true, _) => rhs.flatten(),
                        (_, true) => lhs.flatten(),
                        (_, _) => ExprRet::Fork(Box::new(lhs.flatten()), Box::new(rhs.flatten())),
                    }
                }
                (ExprRet::Multi(lhs_inner), _) => {
                    if lhs_inner.is_empty() {
                        rhs.flatten()
                    } else {
                        ExprRet::Fork(Box::new(lhs.flatten()), Box::new(rhs.flatten()))
                    }
                }
                (_, ExprRet::Multi(rhs_inner)) => {
                    if rhs_inner.is_empty() {
                        lhs.flatten()
                    } else {
                        ExprRet::Fork(Box::new(lhs.flatten()), Box::new(rhs.flatten()))
                    }
                }
                (_, _) => ExprRet::Fork(Box::new(lhs.flatten()), Box::new(rhs.flatten())),
            },
            _ => self,
        }
    }
}

impl<T> ContextBuilder for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
}

pub trait ContextBuilder:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
    fn parse_ctx_statement(
        &mut self,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        if let Some(parent) = parent_ctx {
            match self.node(parent) {
                Node::Context(_) => {
                    let ctx = ContextNode::from(parent.into());
                    if let Some(true) =
                        self.add_if_err(ctx.is_ended(self).into_expr_err(stmt.loc()))
                    {
                        return;
                    }
                    if let Some(live_forks) =
                        self.add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
                    {
                        if live_forks.is_empty() {
                            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
                        } else {
                            live_forks.iter().for_each(|fork_ctx| {
                                self.parse_ctx_stmt_inner(stmt, unchecked, Some(*fork_ctx));
                            });
                        }
                    }
                }
                _ => self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx),
            }
        } else {
            // println!("function entry: {:?}", parent_ctx.map(|ctx| self.node(ctx.into())));
            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_stmt_inner(
        &mut self,
        stmt: &Statement,
        _unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        use Statement::*;
        // if let Some(ctx) = parent_ctx {
        //     if let Node::Context(_) = self.node(ctx) {
        //         println!("ctx: {}, stmt: {:?}", ContextNode::from(ctx.into()).path(self), stmt);
        //     }
        // }

        match stmt {
            Block {
                loc,
                unchecked,
                statements,
            } => {
                tracing::trace!("parsing block");
                let parent = parent_ctx.expect("Free floating contexts shouldn't happen");
                let mut entry_loc = None;
                let mut mods_set = false;
                let ctx_node = match self.node(parent) {
                    Node::Function(fn_node) => {
                        mods_set = fn_node.modifiers_set;
                        entry_loc = Some(fn_node.loc);
                        let ctx = Context::new(
                            FunctionNode::from(parent.into()),
                            self.add_if_err(
                                FunctionNode::from(parent.into())
                                    .name(self)
                                    .into_expr_err(stmt.loc()),
                            )
                            .unwrap(),
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
                let (params, inputs): (Vec<_>, Vec<_>) = self
                    .graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionParam)
                    .map(|edge| FunctionParamNode::from(edge.source()))
                    .collect::<Vec<FunctionParamNode>>()
                    .into_iter()
                    .filter_map(|param_node| {
                        let res = param_node
                            .underlying(self)
                            .into_expr_err(stmt.loc())
                            .cloned();
                        let func_param = self.add_if_err(res)?;
                        if let Some(cvar) = ContextVar::maybe_new_from_func_param(self, func_param)
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );

                            Some((param_node, ContextVarNode::from(cvar_node)))
                        } else {
                            None
                        }
                    })
                    .unzip();

                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionReturn)
                    .map(|edge| FunctionReturnNode::from(edge.source()))
                    .collect::<Vec<FunctionReturnNode>>()
                    .iter()
                    .for_each(|ret_node| {
                        let res = ret_node.underlying(self).into_expr_err(stmt.loc()).cloned();
                        let func_ret = self.add_if_err(res).unwrap();
                        if let Some(cvar) = ContextVar::maybe_new_from_func_ret(self, func_ret) {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                if let Some(fn_loc) = entry_loc {
                    if !mods_set {
                        let parent = FunctionNode::from(parent.into());
                        let _ = self
                            .set_modifiers(parent, ctx_node.into())
                            .map_err(|e| self.add_expr_err(e));
                    }

                    let _ = self
                        .func_call_inner(
                            true,
                            ctx_node.into(),
                            parent.into().into(),
                            fn_loc,
                            inputs,
                            params,
                            None,
                            None,
                        )
                        .map(|ctx| {
                            if ctx.is_killed() {
                                let res = ContextNode::from(ctx_node)
                                    .kill(self, fn_loc)
                                    .into_expr_err(fn_loc);
                                let _ = self.add_if_err(res);
                            }
                        })
                        .map_err(|e| self.add_expr_err(e));

                    return;
                }

                let forks = self
                    .add_if_err(
                        ContextNode::from(ctx_node)
                            .live_forks(self)
                            .into_expr_err(stmt.loc()),
                    )
                    .unwrap();
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
                tracing::trace!("parsing variable definition, {var_decl:?}");
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                let forks = self
                    .add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
                    .unwrap();
                if forks.is_empty() {
                    let _ = self
                        .parse_ctx_expr(&var_decl.ty, ctx)
                        .map(|lhs_paths| {
                            if let Some(rhs) = maybe_expr {
                                let _ = self
                                    .parse_ctx_expr(rhs, ctx)
                                    .map(|rhs_paths| {
                                        self.match_var_def(
                                            var_decl,
                                            *loc,
                                            &lhs_paths,
                                            Some(&rhs_paths),
                                        )
                                        .map(|res| {
                                            if res {
                                                let res = ctx.kill(self, *loc).into_expr_err(*loc);
                                                let _ = self.add_if_err(res);
                                            }
                                        })
                                    })
                                    .map_err(|err| self.add_expr_err(err));
                            } else {
                                let _ = self
                                    .match_var_def(var_decl, *loc, &lhs_paths, None)
                                    .map(|res| {
                                        if res {
                                            let res = ctx.kill(self, *loc).into_expr_err(*loc);
                                            let _ = self.add_if_err(res);
                                        }
                                    })
                                    .map_err(|err| self.add_expr_err(err));
                            }
                        })
                        .map_err(|err| self.add_expr_err(err));
                } else {
                    forks.into_iter().for_each(|ctx| {
                        let _ = self
                            .parse_ctx_expr(&var_decl.ty, ctx)
                            .map(|lhs_paths| {
                                if let Some(rhs) = maybe_expr {
                                    let _ =
                                        self.parse_ctx_expr(rhs, ctx)
                                            .map(|rhs_paths| {
                                                self.match_var_def(
                                                    var_decl,
                                                    *loc,
                                                    &lhs_paths,
                                                    Some(&rhs_paths),
                                                )
                                                .map(|res| {
                                                    if res {
                                                        let res = ctx
                                                            .kill(self, *loc)
                                                            .into_expr_err(*loc);
                                                        let _ = self.add_if_err(res);
                                                    }
                                                })
                                            })
                                            .map_err(|err| self.add_expr_err(err));
                                } else {
                                    let _ = self
                                        .match_var_def(var_decl, *loc, &lhs_paths, None)
                                        .map(|res| {
                                            if res {
                                                let res = ctx.kill(self, *loc).into_expr_err(*loc);
                                                let _ = self.add_if_err(res);
                                            }
                                        })
                                        .map_err(|err| self.add_expr_err(err));
                                }
                            })
                            .map_err(|err| self.add_expr_err(err));
                    });
                }
            }
            Args(_loc, _args) => {
                tracing::trace!("parsing args, {_args:?}");
            }
            If(loc, if_expr, true_expr, maybe_false_expr) => {
                tracing::trace!("parsing if, {if_expr:?}");
                let ctx = ContextNode::from(parent_ctx.expect("Dangling if statement").into());
                let forks = self
                    .add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
                    .unwrap();
                if forks.is_empty() {
                    let _ = self
                        .cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, ctx)
                        .map_err(|e| self.add_expr_err(e));
                } else {
                    forks.into_iter().for_each(|parent| {
                        let _ = self
                            .cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, parent)
                            .map_err(|e| self.add_expr_err(e));
                    });
                }
            }
            While(loc, cond, body) => {
                tracing::trace!("parsing while, {cond:?}");
                if let Some(parent) = parent_ctx {
                    let res = self.while_loop(*loc, parent.into().into(), cond, body);
                    let _ = self.add_if_err(res);
                }
            }
            Expression(loc, expr) => {
                tracing::trace!("parsing expr, {expr:?}");
                if let Some(parent) = parent_ctx {
                    let _ = self
                        .parse_ctx_expr(expr, ContextNode::from(parent.into()))
                        .map(|ctx| {
                            if ctx.is_killed() {
                                let res = ContextNode::from(parent.into())
                                    .kill(self, *loc)
                                    .into_expr_err(*loc);
                                let _ = self.add_if_err(res);
                            }
                        })
                        .map_err(|e| self.add_expr_err(e));
                }
            }
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {
                tracing::trace!("parsing for loop");
                if let Some(parent) = parent_ctx {
                    let res = self.for_loop(
                        *loc,
                        parent.into().into(),
                        maybe_for_start,
                        maybe_for_middle,
                        maybe_for_end,
                        maybe_for_body,
                    );
                    let _ = self.add_if_err(res);
                }
            }
            DoWhile(_loc, _while_stmt, _while_expr) => {
                todo!("do while not supported");
            }
            Continue(_loc) => {
                tracing::trace!("parsing continue");
                // TODO: We cheat in loops by just widening so continues dont matter yet
            }
            Break(_loc) => {
                tracing::trace!("parsing break");
                // TODO: We cheat in loops by just widening so breaks dont matter yet
            }
            Assembly {
                loc: _,
                dialect: _,
                flags: _,
                block: yul_block,
            } => {
                tracing::trace!("parsing assembly");
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                self.parse_ctx_yul_statement(&YulStatement::Block(yul_block.clone()), ctx);
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about any variables anymore.
                // We should evaluate what variables are modified and consider mstores and sstores.

                // let vars = ctx.local_vars(self);
                // vars.iter().for_each(|var| {
                //     // widen to max range
                //     let latest_var = var.latest_version(self);
                //     let res = latest_var.ty(self).into_expr_err(stmt.loc()).cloned();
                //     if let Some(r) = self.add_if_err(res).unwrap().default_range(self).unwrap() {
                //         let new_var = self.advance_var_in_ctx(latest_var, *loc, ctx).unwrap();
                //         let res = new_var.set_range_min(self, r.min).into_expr_err(*loc);
                //         let _ = self.add_if_err(res);
                //         let res = new_var.set_range_max(self, r.max).into_expr_err(*loc);
                //         let _ = self.add_if_err(res);
                //     }
                // });
            }
            Return(loc, maybe_ret_expr) => {
                tracing::trace!("parsing return");
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let forks = self
                            .add_if_err(
                                ContextNode::from(parent.into())
                                    .live_forks(self)
                                    .into_expr_err(stmt.loc()),
                            )
                            .unwrap();
                        if forks.is_empty() {
                            let _ = self
                                .parse_ctx_expr(ret_expr, ContextNode::from(parent.into()))
                                .map(|paths| {
                                    let paths = paths.flatten();
                                    if paths.is_killed() {
                                        let res = ContextNode::from(parent.into())
                                            .kill(self, *loc)
                                            .into_expr_err(*loc);
                                        let _ = self.add_if_err(res);
                                        return;
                                    }
                                    self.return_match(loc, &paths);
                                })
                                .map_err(|e| self.add_expr_err(e));
                        } else {
                            forks.into_iter().for_each(|parent| {
                                let _ = self
                                    .parse_ctx_expr(ret_expr, parent)
                                    .map(|paths| {
                                        let paths = paths.flatten();
                                        if paths.is_killed() {
                                            let res = parent.kill(self, *loc).into_expr_err(*loc);
                                            let _ = self.add_if_err(res);
                                            return;
                                        }
                                        self.return_match(loc, &paths);
                                    })
                                    .map_err(|e| self.add_expr_err(e));
                            });
                        }
                    }
                }
            }
            Revert(loc, _maybe_err_path, _exprs) => {
                tracing::trace!("parsing revert");
                if let Some(parent) = parent_ctx {
                    let parent = ContextNode::from(parent.into());
                    let forks = self
                        .add_if_err(parent.live_forks(self).into_expr_err(stmt.loc()))
                        .unwrap();
                    if forks.is_empty() {
                        let res = parent.kill(self, *loc).into_expr_err(*loc);
                        let _ = self.add_if_err(res);
                    } else {
                        forks.into_iter().for_each(|parent| {
                            let res = parent.kill(self, *loc).into_expr_err(*loc);
                            let _ = self.add_if_err(res);
                        });
                    }
                }
            }
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {
                tracing::trace!("parsing named revert");
                todo!("revert named args")
            }
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        };

        if let Some(parent) = parent_ctx {
            if let Node::Context(c) = self.node(parent.into()) {
                let adjusts = c.post_statement_range_adjs.clone();
                adjusts.into_iter().for_each(|(var, loc, increment)| {
                    let one_node = self.add_node(Node::Concrete(Concrete::from(U256::from(1))));
                    let new_var = self
                        .add_if_err(
                            ContextVar::new_from_concrete(Loc::Implicit, one_node.into(), self)
                                .into_expr_err(stmt.loc()),
                        )
                        .unwrap();
                    let one_node = self.add_node(Node::ContextVar(new_var));
                    let _ = self
                        .op(
                            loc,
                            var.latest_version(self),
                            one_node.into(),
                            parent.into().into(),
                            if increment {
                                RangeOp::Add
                            } else {
                                RangeOp::Sub
                            },
                            true,
                        )
                        .map_err(|e| self.add_expr_err(e));
                });
                ContextNode::from(parent.into())
                    .underlying_mut(self)
                    .unwrap()
                    .post_statement_range_adjs = vec![];
            }
        }
    }

    fn return_match(&mut self, loc: &Loc, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) | ExprRet::SingleLiteral((ctx, expr)) => {
                self.add_edge(
                    ContextVarNode::from(*expr).latest_version(self),
                    *ctx,
                    Edge::Context(ContextEdge::Return),
                );
                let res = ctx
                    .add_return_node(*loc, ContextVarNode::from(*expr).latest_version(self), self)
                    .into_expr_err(*loc);
                let _ = self.add_if_err(res);
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    self.return_match(loc, expr_ret);
                });
            }
            ExprRet::Fork(world1, world2) => {
                self.return_match(loc, world1);
                self.return_match(loc, world2);
            }
        }
    }

    fn match_var_def(
        &mut self,
        var_decl: &VariableDeclaration,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: Option<&ExprRet>,
    ) -> Result<bool, ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::CtxKilled, _) | (_, Some(ExprRet::CtxKilled)) => Ok(true),
            (ExprRet::Single((_lhs_ctx, ty)), Some(ExprRet::SingleLiteral((rhs_ctx, rhs)))) => {
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar.literal_cast_from_ty(ty, self).into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_var_def(
                    var_decl,
                    loc,
                    lhs_paths,
                    Some(&ExprRet::Single((*rhs_ctx, rhs_cvar.into()))),
                )
            }
            (ExprRet::Single((_lhs_ctx, ty)), Some(ExprRet::Single((rhs_ctx, rhs)))) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.clone(),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                self.add_edge(lhs, *rhs_ctx, Edge::Context(ContextEdge::Variable));
                let rhs = ContextVarNode::from(*rhs);

                fn match_assign_ret(analyzer: &mut impl GraphLike, ret: ExprRet) {
                    match ret {
                        ExprRet::Single((ctx, new_lhs))
                        | ExprRet::SingleLiteral((ctx, new_lhs)) => {
                            analyzer.add_edge(new_lhs, ctx, Edge::Context(ContextEdge::Variable));
                        }
                        ExprRet::Multi(inner) => inner
                            .into_iter()
                            .for_each(|i| match_assign_ret(analyzer, i)),
                        ExprRet::Fork(w1, w2) => {
                            match_assign_ret(analyzer, *w1);
                            match_assign_ret(analyzer, *w2);
                        }
                        ExprRet::CtxKilled => {}
                    }
                }

                let ret = self.assign(loc, lhs, rhs, *rhs_ctx)?;
                match_assign_ret(self, ret);

                Ok(false)
            }
            (ExprRet::Single((lhs_ctx, ty)), None) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.clone(),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                self.add_edge(lhs, *lhs_ctx, Edge::Context(ContextEdge::Variable));
                Ok(false)
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), Some(ExprRet::Multi(rhs_sides))) => {
                Ok(rhs_sides
                    .iter()
                    .map(|expr_ret| self.match_var_def(var_decl, loc, l, Some(expr_ret)))
                    .collect::<Result<Vec<_>, ExprErr>>()?
                    .iter()
                    .all(|e| *e))
            }
            (ExprRet::Multi(lhs_sides), r @ Some(ExprRet::Single(_))) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(var_decl, loc, expr_ret, r))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), None) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(var_decl, loc, expr_ret, None))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), Some(ExprRet::Multi(rhs_sides))) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    Ok(lhs_sides
                        .iter()
                        .zip(rhs_sides.iter())
                        .map(|(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_var_def(var_decl, loc, lhs_expr_ret, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                } else {
                    Ok(rhs_sides
                        .iter()
                        .map(|rhs_expr_ret| {
                            self.match_var_def(var_decl, loc, lhs_paths, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                }
            }
            (
                ExprRet::Fork(lhs_world1, lhs_world2),
                Some(ExprRet::Fork(rhs_world1, rhs_world2)),
            ) => Ok(
                self.match_var_def(var_decl, loc, lhs_world1, Some(rhs_world1))?
                    && self.match_var_def(var_decl, loc, lhs_world1, Some(rhs_world2))?
                    && self.match_var_def(var_decl, loc, lhs_world2, Some(rhs_world1))?
                    && self.match_var_def(var_decl, loc, lhs_world2, Some(rhs_world2))?,
            ),
            (l @ ExprRet::Single(_), Some(ExprRet::Fork(world1, world2))) => Ok(self
                .match_var_def(var_decl, loc, l, Some(world1))?
                && self.match_var_def(var_decl, loc, l, Some(world2))?),
            (m @ ExprRet::Multi(_), Some(ExprRet::Fork(world1, world2))) => Ok(self
                .match_var_def(var_decl, loc, m, Some(world1))?
                && self.match_var_def(var_decl, loc, m, Some(world2))?),
            (e, f) => Err(ExprErr::Todo(
                loc,
                "Unhandled ExprRet combination in `match_var_def`".to_string(),
            )),
        }
    }

    fn match_expr(&mut self, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) | ExprRet::SingleLiteral((ctx, expr)) => {
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

    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> Result<ExprRet, ExprErr> {
        if ctx.is_ended(self).into_expr_err(expr.loc())? {
            return Ok(ExprRet::CtxKilled);
        }

        if ctx.live_forks(self).into_expr_err(expr.loc())?.is_empty() {
            self.parse_ctx_expr_inner(expr, ctx)
        } else {
            let rets: Vec<ExprRet> = ctx
                .live_forks(self)
                .into_expr_err(expr.loc())?
                .iter()
                .map(|fork_ctx| self.parse_ctx_expr(expr, *fork_ctx))
                .collect::<Result<_, ExprErr>>()?;
            if rets.len() == 1 {
                Ok(rets.into_iter().take(1).next().unwrap())
            } else {
                Ok(ExprRet::Multi(rets))
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    fn parse_ctx_expr_inner(
        &mut self,
        expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        use Expression::*;
        // println!("ctx: {}, {:?}", ctx.underlying(self).unwrap().path, expr);
        match expr {
            // literals
            NumberLiteral(loc, int, exp, _unit) => self.number_literal(ctx, *loc, int, exp, false),
            AddressLiteral(loc, addr) => self.address_literal(ctx, *loc, addr),
            StringLiteral(lits) => Ok(ExprRet::Multi(
                lits.iter()
                    .map(|lit| self.string_literal(ctx, lit.loc, &lit.string))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            BoolLiteral(loc, b) => self.bool_literal(ctx, *loc, *b),
            HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
            HexLiteral(hexes) => self.hex_literals(ctx, hexes),
            RationalNumberLiteral(_, _, _, _, _) => todo!("Rational literal"),
            Negate(_loc, expr) => match &**expr {
                NumberLiteral(loc, int, exp, _unit) => {
                    self.number_literal(ctx, *loc, int, exp, true)
                }
                HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, true),
                e => todo!("UnaryMinus unexpected rhs: {e:?}"),
            },
            UnaryPlus(_loc, e) => todo!("UnaryPlus unexpected rhs: {e:?}"),

            // Binary ops
            Power(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Exp, false)
            }
            Add(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Add, false)
            }
            AssignAdd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Add, true)
            }
            Subtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Sub, false)
            }
            AssignSubtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Sub, true)
            }
            Multiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mul, false)
            }
            AssignMultiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mul, true)
            }
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div, false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div, true)
            }
            Modulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mod, false)
            }
            AssignModulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mod, true)
            }
            ShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shl, false)
            }
            AssignShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shl, true)
            }
            ShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shr, false)
            }
            AssignShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shr, true)
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {
                self.cond_op_expr(*loc, if_expr, true_expr, false_expr, ctx)
            }

            // Bitwise ops
            BitwiseAnd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitAnd, false)
            }
            AssignAnd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitAnd, true)
            }
            BitwiseXor(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitXor, false)
            }
            AssignXor(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitXor, true)
            }
            BitwiseOr(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitOr, false)
            }
            AssignOr(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitOr, true)
            }
            BitwiseNot(_loc, _lhs_expr) => {
                todo!("Bitwise not")
                // self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitNot, false)
            }

            // assign
            Assign(loc, lhs_expr, rhs_expr) => self.assign_exprs(*loc, lhs_expr, rhs_expr, ctx),
            List(loc, params) => self.list(ctx, *loc, params),
            // array
            ArraySubscript(_loc, ty_expr, None) => self.array_ty(ty_expr, ctx),
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.index_into_array(*loc, ty_expr, index_expr, ctx)
            }
            ArraySlice(_loc, _lhs_expr, _maybe_middle_expr, _maybe_rhs) => todo!("Array slice"),
            ArrayLiteral(_, _) => todo!("Array literal"),

            // Comparator
            Equal(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Eq, rhs, ctx),
            NotEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Neq, rhs, ctx),
            Less(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Lt, rhs, ctx),
            More(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Gt, rhs, ctx),
            LessEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Lte, rhs, ctx),
            MoreEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Gte, rhs, ctx),

            // Logical
            Not(loc, expr) => self.not(*loc, expr, ctx),
            And(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::And, rhs, ctx),
            Or(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Or, rhs, ctx),

            // Function calls
            FunctionCallBlock(loc, _func_expr, _input_exprs) => {
                Err(ExprErr::Todo(*loc, "Function call block".to_string()))
            }
            NamedFunctionCall(loc, func_expr, input_args) => {
                self.named_fn_call_expr(ctx, loc, func_expr, input_args)
            }
            FunctionCall(loc, func_expr, input_exprs) => {
                self.fn_call_expr(ctx, loc, func_expr, input_exprs)
            }
            // member
            New(_loc, expr) => self.parse_ctx_expr(expr, ctx),
            This(loc) => {
                let var = ContextVar::new_from_contract(
                    *loc,
                    ctx.associated_contract(self).into_expr_err(*loc)?,
                    self,
                )
                .into_expr_err(*loc)?;
                let cvar = self.add_node(Node::ContextVar(var));
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                Ok(ExprRet::Single((ctx, cvar)))
            }
            MemberAccess(loc, member_expr, ident) => {
                self.member_access(*loc, member_expr, ident, ctx)
            }

            Delete(loc, expr) => {
                let ret = self.parse_ctx_expr(expr, ctx)?;
                fn delete_match(
                    loc: &Loc,
                    analyzer: &mut (impl GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr>),
                    ret: ExprRet,
                ) -> ExprRet {
                    match ret {
                        ExprRet::CtxKilled => ExprRet::CtxKilled,
                        ExprRet::Single((ctx, cvar)) | ExprRet::SingleLiteral((ctx, cvar)) => {
                            let mut new_var =
                                analyzer.advance_var_in_ctx(cvar.into(), *loc, ctx).unwrap();
                            let res = new_var.sol_delete_range(analyzer).into_expr_err(*loc);
                            let _ = analyzer.add_if_err(res);
                            ExprRet::Single((ctx, new_var.into()))
                        }
                        ExprRet::Multi(inner) => ExprRet::Multi(
                            inner
                                .iter()
                                .map(|i| delete_match(loc, analyzer, i.clone()))
                                .collect(),
                        ),
                        ExprRet::Fork(w1, w2) => ExprRet::Fork(
                            Box::new(delete_match(loc, analyzer, *w1)),
                            Box::new(delete_match(loc, analyzer, *w2)),
                        ),
                    }
                }
                Ok(delete_match(loc, self, ret))
            }

            // de/increment stuff
            PreIncrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx)?;
                self.match_in_de_crement(true, true, *loc, &resp)
            }
            PostIncrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx)?;
                self.match_in_de_crement(false, true, *loc, &resp)
            }
            PreDecrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx)?;
                self.match_in_de_crement(true, false, *loc, &resp)
            }
            PostDecrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx)?;
                self.match_in_de_crement(false, false, *loc, &resp)
            }

            // Misc.
            Variable(ident) => self.variable(ident, ctx),
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        Ok(ExprRet::Single((ctx, *idx)))
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        Ok(ExprRet::Single((ctx, idx)))
                    }
                } else {
                    todo!("??")
                }
            }
            Parenthesis(_loc, expr) => self.parse_ctx_expr(expr, ctx),
        }
    }

    fn match_in_de_crement(
        &mut self,
        pre: bool,
        increment: bool,
        loc: Loc,
        rhs: &ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match rhs {
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
            ExprRet::SingleLiteral((ctx, var)) => {
                let res = ContextVarNode::from(*var)
                    .try_increase_size(self)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_in_de_crement(pre, increment, loc, &ExprRet::Single((*ctx, *var)))
            }
            ExprRet::Single((ctx, var)) => {
                let cvar = ContextVarNode::from(*var);
                let elem = Elem::Dynamic(Dynamic::new(cvar.into()));
                let one = Elem::from(Concrete::from(U256::from(1))).cast(elem);
                if let Some(r) = cvar.range(self).into_expr_err(loc)? {
                    if increment {
                        if pre {
                            let new_cvar = self.advance_var_in_ctx(cvar, loc, *ctx)?;
                            let res = new_cvar
                                .set_range_min(self, r.min + one.clone())
                                .into_expr_err(loc);
                            let _ = self.add_if_err(res);
                            let res = new_cvar.set_range_max(self, r.max + one).into_expr_err(loc);
                            let _ = self.add_if_err(res);
                            Ok(ExprRet::Single((*ctx, new_cvar.into())))
                        } else {
                            ctx.underlying_mut(self)
                                .into_expr_err(loc)?
                                .post_statement_range_adjs
                                .push((cvar, loc, increment));
                            Ok(ExprRet::Single((*ctx, cvar.into())))
                        }
                    } else if pre {
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, *ctx)?;
                        let res = new_cvar
                            .set_range_min(self, r.min - one.clone())
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        let res = new_cvar.set_range_max(self, r.max - one).into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        Ok(ExprRet::Single((*ctx, new_cvar.into())))
                    } else {
                        ctx.underlying_mut(self)
                            .into_expr_err(loc)?
                            .post_statement_range_adjs
                            .push((cvar, loc, increment));
                        Ok(ExprRet::Single((*ctx, cvar.into())))
                    }
                } else {
                    panic!("No range in post-increment")
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .iter()
                    .map(|expr| self.match_in_de_crement(pre, increment, loc, expr))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_in_de_crement(pre, increment, loc, w1)?),
                Box::new(self.match_in_de_crement(pre, increment, loc, w2)?),
            )),
        }
    }

    fn assign_exprs(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let lhs_paths = self.parse_ctx_expr(lhs_expr, ctx)?.flatten();
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx)?.flatten();
        self.match_assign_sides(loc, &lhs_paths, &rhs_paths)
    }

    fn match_assign_sides(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::CtxKilled, _) | (_, ExprRet::CtxKilled) => Ok(ExprRet::CtxKilled),
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar
                    .literal_cast_from(&lhs_cvar, self)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.assign(loc, lhs_cvar, rhs_cvar, *rhs_ctx)
            }
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                self.assign(loc, lhs_cvar, rhs_cvar, *rhs_ctx)
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => {
                Ok(ExprRet::Multi(
                    rhs_sides
                        .iter()
                        .map(|expr_ret| self.match_assign_sides(loc, l, expr_ret))
                        .collect::<Result<_, ExprErr>>()?,
                ))
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                Ok(ExprRet::Multi(
                    lhs_sides
                        .iter()
                        .map(|expr_ret| self.match_assign_sides(loc, expr_ret, r))
                        .collect::<Result<_, ExprErr>>()?,
                ))
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    Ok(ExprRet::Multi(
                        lhs_sides
                            .iter()
                            .zip(rhs_sides.iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.match_assign_sides(loc, lhs_expr_ret, rhs_expr_ret)
                            })
                            .collect::<Result<_, ExprErr>>()?,
                    ))
                } else {
                    Ok(ExprRet::Multi(
                        rhs_sides
                            .iter()
                            .map(|rhs_expr_ret| {
                                self.match_assign_sides(loc, lhs_paths, rhs_expr_ret)
                            })
                            .collect::<Result<_, ExprErr>>()?,
                    ))
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                Ok(ExprRet::Fork(
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world1)?),
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world2)?),
                    )),
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world1)?),
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world2)?),
                    )),
                ))
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => Ok(ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, l, world1)?),
                Box::new(self.match_assign_sides(loc, l, world2)?),
            )),
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => Ok(ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, m, world1)?),
                Box::new(self.match_assign_sides(loc, m, world2)?),
            )),
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    fn assign(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        // println!("rhs_range: {:?}", rhs_cvar.range(self));
        let (new_lower_bound, new_upper_bound): (Elem<Concrete>, Elem<Concrete>) = (
            Elem::Dynamic(Dynamic::new(rhs_cvar.latest_version(self).into())),
            Elem::Dynamic(Dynamic::new(rhs_cvar.latest_version(self).into())),
        );

        let new_lhs = self.advance_var_in_ctx(lhs_cvar.latest_version(self), loc, ctx)?;
        if !lhs_cvar.ty_eq(&rhs_cvar, self).into_expr_err(loc)? {
            let cast_to_min = match lhs_cvar.range_min(self).into_expr_err(loc)? {
                Some(v) => v,
                None => {
                    return Err(ExprErr::BadRange(
                        loc,
                        format!(
                            "No range during cast? {:?}",
                            lhs_cvar.underlying(self).unwrap()
                        ),
                    ))
                }
            };

            let cast_to_max = match lhs_cvar.range_max(self).into_expr_err(loc)? {
                Some(v) => v,
                None => {
                    return Err(ExprErr::BadRange(
                        loc,
                        format!(
                            "No range during cast? {:?}",
                            lhs_cvar.underlying(self).unwrap()
                        ),
                    ))
                }
            };

            let _ = new_lhs.try_set_range_min(self, new_lower_bound.cast(cast_to_min));
            let _ = new_lhs.try_set_range_max(self, new_upper_bound.cast(cast_to_max));
        } else {
            let _ = new_lhs.try_set_range_min(self, new_lower_bound);
            let _ = new_lhs.try_set_range_max(self, new_upper_bound);
        }
        if let Some(rhs_range) = rhs_cvar.range(self).into_expr_err(loc)? {
            let res = new_lhs
                .try_set_range_exclusions(self, rhs_range.exclusions)
                .into_expr_err(loc);
            let _ = self.add_if_err(res);
        }

        if let Some(arr) = lhs_cvar.index_to_array(self) {
            if let Some(index) = lhs_cvar.index_access_to_index(self) {
                let next_arr = self.advance_var_in_ctx(arr, loc, ctx)?;
                if next_arr
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .is_dyn_builtin(self)
                    .into_expr_err(loc)?
                {
                    if let Some(r) = next_arr.range(self).into_expr_err(loc)? {
                        let min = r.evaled_range_min(self).into_expr_err(loc)?;
                        let max = r.evaled_range_max(self).into_expr_err(loc)?;

                        if let Some(mut rd) = min.maybe_range_dyn() {
                            rd.val.insert(
                                Elem::Dynamic(Dynamic::new(index.into())),
                                Elem::Dynamic(Dynamic::new(rhs_cvar.into())),
                            );
                            let res = next_arr
                                .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc);
                            let _ = self.add_if_err(res);
                        }

                        if let Some(mut rd) = max.maybe_range_dyn() {
                            rd.val.insert(
                                Elem::Dynamic(Dynamic::new(index.into())),
                                Elem::Dynamic(Dynamic::new(rhs_cvar.into())),
                            );
                            let res = next_arr
                                .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc);
                            let _ = self.add_if_err(res);
                        }
                    }
                }
            }
        }

        Ok(ExprRet::Single((ctx, new_lhs.into())))
    }

    fn advance_var_in_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<ContextVarNode, ExprErr> {
        if let Some(cvar) = cvar_node.next_version(self) {
            panic!(
                "Not latest version of: {}",
                cvar.display_name(self).unwrap()
            );
        }
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
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

        Ok(ContextVarNode::from(new_cvarnode))
    }

    fn advance_var_underlying(&mut self, cvar_node: ContextVarNode, loc: Loc) -> &mut ContextVar {
        assert_eq!(None, cvar_node.next_version(self));
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .unwrap()
            .clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode)
            .underlying_mut(self)
            .unwrap()
    }
}
