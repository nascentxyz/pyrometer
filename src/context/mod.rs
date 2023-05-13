use crate::context::yul::YulBuilder;
use ethers_core::types::I256;

use ethers_core::types::U256;

use shared::analyzer::GraphError;
use shared::analyzer::GraphLike;
use shared::context::*;
use solang_parser::helpers::CodeLocation;
use solang_parser::pt::YulStatement;

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
                    if !ctx.killed_or_ret(self).unwrap() {
                        if let Some(live_edges) =
                            self.add_if_err(ctx.live_edges(self).into_expr_err(stmt.loc()))
                        {
                            if live_edges.is_empty() {
                                self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
                            } else {
                                live_edges.iter().for_each(|fork_ctx| {
                                    self.parse_ctx_stmt_inner(stmt, unchecked, Some(*fork_ctx));
                                });
                            }
                        }
                    }
                }
                _ => self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx),
            }
        } else {
            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_stmt_inner(
        &mut self,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        use Statement::*;
        // println!("stmt: {:#?}, node: {:#?}", stmt, if let Some(node) = parent_ctx { Some(self.node(node.into())) } else { None});
        // if let Some(ctx) = parent_ctx {
        //     if let Node::Context(_) = self.node(ctx) {
        //     println!("ctx: {}, {:#?}", ContextNode::from(ctx.into()).path(self), stmt);
        //     }
        // }
        // println!("START STMT");

        // at the end of a statement we shouldn't have anything in the stack?
        if let Some(ctx) = parent_ctx {
            if let Node::Context(_) = self.node(ctx) {
                let c = ContextNode::from(ctx.into());
                c.pop_expr_latest(stmt.loc(), self);
                // println!("popped");
                if unchecked {
                    c.set_unchecked(self);
                } else {
                    c.unset_unchecked(self);
                }

                if c.killed_or_ret(self).unwrap() {
                    return;
                }
            }
        }

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
                        // println!("{mods_set:?}, {:?}", fn_node.name);
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
                            ContextNode::from(ctx_node)
                                .add_var(cvar_node.into(), self)
                                .unwrap();
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
                            ContextNode::from(ctx_node)
                                .add_var(cvar_node.into(), self)
                                .unwrap();
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

                    let res = self.func_call_inner(
                        true,
                        ctx_node.into(),
                        parent.into().into(),
                        fn_loc,
                        inputs,
                        params,
                        None,
                        None,
                    );
                    if self.widen_if_limit_hit(ctx_node.into(), res) {
                        return;
                    }
                    let res = self.apply_to_edges(ctx_node.into(), *loc, &|analyzer, ctx, loc| {
                        if ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                            tracing::trace!("killing due to bad funciton call");
                            let res = ContextNode::from(ctx_node)
                                .kill(
                                    analyzer,
                                    fn_loc,
                                    ctx.underlying(analyzer).unwrap().killed.unwrap().1,
                                )
                                .into_expr_err(fn_loc);
                            let _ = analyzer.add_if_err(res);
                        }
                        Ok(())
                    });

                    if self.widen_if_limit_hit(ctx_node.into(), res) {
                        return;
                    }

                    return;
                }

                let res = self.apply_to_edges(ctx_node.into(), *loc, &|analyzer, ctx, _loc| {
                    statements
                        .iter()
                        .for_each(|stmt| analyzer.parse_ctx_statement(stmt, *unchecked, Some(ctx)));
                    Ok(())
                });
                if self.widen_if_limit_hit(ctx_node.into(), res) {}
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                tracing::trace!(
                    "parsing variable definition, {:?} {var_decl:?}",
                    ctx.path(self)
                );

                if let Some(rhs) = maybe_expr {
                    match self.parse_ctx_expr(rhs, ctx) {
                        Ok(()) => {
                            let res = self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                if !ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                        return Err(ExprErr::NoRhs(loc, format!("Variable definition had no right hand side, {}", ctx.path(analyzer))))
                                    };

                                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                                        return Ok(());
                                    }

                                    analyzer.parse_ctx_expr(&var_decl.ty, ctx)?;
                                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                            return Err(ExprErr::NoLhs(loc, "Variable definition had no left hand side".to_string()))
                                        };

                                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                                            return Ok(());
                                        }
                                        analyzer.match_var_def(ctx, var_decl, loc, &lhs_paths, Some(&rhs_paths))?;
                                        Ok(())
                                    })
                                } else {
                                    Ok(())
                                }
                            });
                            let _ = self.widen_if_limit_hit(ctx, res);
                        }
                        ret => {
                            let _ = self.widen_if_limit_hit(ctx, ret);
                        }
                    }
                } else {
                    let res = self.parse_ctx_expr(&var_decl.ty, ctx);
                    if self.widen_if_limit_hit(ctx, res) {
                        return;
                    }
                    let res = self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Variable definition had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.match_var_def(ctx, var_decl, loc, &lhs_paths, None)?;
                        Ok(())
                    });
                    let _ = self.widen_if_limit_hit(ctx, res);
                }
            }
            Args(_loc, _args) => {
                tracing::trace!("parsing args, {_args:?}");
            }
            If(loc, if_expr, true_expr, maybe_false_expr) => {
                tracing::trace!("parsing if, {if_expr:?}");
                let ctx = ContextNode::from(parent_ctx.expect("Dangling if statement").into());
                let res = self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    analyzer.cond_op_stmt(loc, if_expr, true_expr, maybe_false_expr, ctx)
                });
                let _ = self.widen_if_limit_hit(ctx, res);
            }
            While(loc, cond, body) => {
                tracing::trace!("parsing while, {cond:?}");
                if let Some(parent) = parent_ctx {
                    let res = self.apply_to_edges(
                        ContextNode::from(parent.into()),
                        *loc,
                        &|analyzer, ctx, loc| analyzer.while_loop(loc, ctx, cond, body),
                    );
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
            }
            Expression(loc, expr) => {
                tracing::trace!("parsing expr, {expr:?}");
                if let Some(parent) = parent_ctx {
                    let ctx = parent.into().into();
                    match self.parse_ctx_expr(expr, ctx) {
                        Ok(()) => {
                            let res = self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                if ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                                    tracing::trace!("killing due to bad expr");
                                    ContextNode::from(parent.into())
                                        .kill(
                                            analyzer,
                                            loc,
                                            ctx.underlying(analyzer).unwrap().killed.unwrap().1,
                                        )
                                        .into_expr_err(loc)?;
                                }
                                Ok(())
                            });
                            let _ = self.widen_if_limit_hit(ctx, res);
                        }
                        e => {
                            let _ = self.widen_if_limit_hit(ctx, e);
                        }
                    }
                }
            }
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {
                tracing::trace!("parsing for loop");
                if let Some(parent) = parent_ctx {
                    let res =
                        self.apply_to_edges(parent.into().into(), *loc, &|analyzer, ctx, loc| {
                            analyzer.for_loop(
                                loc,
                                ctx,
                                maybe_for_start,
                                maybe_for_middle,
                                maybe_for_end,
                                maybe_for_body,
                            )
                        });
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
            }
            DoWhile(loc, while_stmt, while_expr) => {
                tracing::trace!("parsing `do while`, {while_expr:?}");
                if let Some(parent) = parent_ctx {
                    let res = self.apply_to_edges(
                        ContextNode::from(parent.into()),
                        *loc,
                        &|analyzer, ctx, loc| analyzer.while_loop(loc, ctx, while_expr, while_stmt),
                    );
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
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
                loc,
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
                let res = self.apply_to_edges(ctx, *loc, &|analyzer, ctx, _loc| {
                    analyzer.parse_ctx_yul_statement(&YulStatement::Block(yul_block.clone()), ctx);
                    Ok(())
                });
                let _ = self.widen_if_limit_hit(ctx, res);
            }
            Return(loc, maybe_ret_expr) => {
                tracing::trace!("parsing return");
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let res = self.parse_ctx_expr(ret_expr, parent.into().into());
                        if self.widen_if_limit_hit(parent.into().into(), res) {
                            return;
                        }
                        let res = self.apply_to_edges(parent.into().into(), *loc, &|analyzer, ctx, loc| {
                            let Ok(Some(ret)) = ctx.pop_expr_latest(loc, analyzer) else {
                                return Err(ExprErr::NoLhs(loc, "Return did not have a associated expression".to_string()));
                            };

                            if matches!(ret, ExprRet::CtxKilled(_)) {
                                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                                return Ok(());
                            }

                            let paths = ret.flatten();
                            if paths.is_killed() {
                                tracing::trace!("killing due to bad return");
                                let res = ContextNode::from(parent.into())
                                    .kill(analyzer, loc, paths.killed_kind().unwrap())
                                    .into_expr_err(loc);
                                let _ = analyzer.add_if_err(res);
                                return Ok(());
                            }
                            analyzer.return_match(ctx, &loc, &paths);
                            Ok(())
                        });
                        let _ = self.widen_if_limit_hit(parent.into().into(), res);
                    }
                }
            }
            Revert(loc, _maybe_err_path, _exprs) => {
                tracing::trace!("parsing revert");
                if let Some(parent) = parent_ctx {
                    let parent = ContextNode::from(parent.into());
                    let res = self.apply_to_edges(parent, *loc, &|analyzer, ctx, loc| {
                        let res = ctx
                            .kill(analyzer, loc, KilledKind::Revert)
                            .into_expr_err(loc);
                        let _ = analyzer.add_if_err(res);
                        Ok(())
                    });
                    let _ = self.add_if_err(res);
                }
            }
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {
                tracing::trace!("parsing named revert");
                todo!("revert named args")
            }
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }

    fn widen_if_limit_hit(&mut self, _ctx: ContextNode, maybe_err: Result<(), ExprErr>) -> bool {
        match maybe_err {
            Err(e @ ExprErr::GraphError(_, GraphError::MaxStackWidthReached(..), ..)) => {
                // TODO: we should ideally peak at each if statement body and only widen variables referenced in there
                // but for now we just delete the forks, and reset all local variables
                self.add_expr_err(e);
                true
            }
            Err(e) => {
                self.add_expr_err(e);
                false
            }
            _ => false,
        }
    }

    fn return_match(&mut self, ctx: ContextNode, loc: &Loc, paths: &ExprRet) {
        println!("return match: {}", ctx.path(self));
        match paths {
            ExprRet::CtxKilled(kind) => {
                let _ = ctx.kill(self, *loc, *kind);
            }
            ExprRet::Single(expr) | ExprRet::SingleLiteral(expr) => {
                let latest = ContextVarNode::from(*expr).latest_version(self);
                // let ret = self.advance_var_in_ctx(latest, *loc, *ctx);
                let path = ctx.path(self);
                let res = latest.underlying_mut(self).into_expr_err(*loc);
                match res {
                    Ok(var) => {
                        tracing::trace!("Returning: {}, {}", path, var.display_name);
                        var.is_return = true;

                        self.add_edge(latest, ctx, Edge::Context(ContextEdge::Return));

                        let res = ctx.add_return_node(*loc, latest, self).into_expr_err(*loc);
                        // ctx.kill(self, *loc, KilledKind::Ended);
                        let _ = self.add_if_err(res);
                    }
                    Err(e) => self.add_expr_err(e),
                }
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    self.return_match(ctx, loc, expr_ret);
                });
            }
            ExprRet::Null => {}
        }
    }

    fn match_var_def(
        &mut self,
        ctx: ContextNode,
        var_decl: &VariableDeclaration,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: Option<&ExprRet>,
    ) -> Result<bool, ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::CtxKilled(kind), _) | (_, Some(ExprRet::CtxKilled(kind))) => {
                ctx.kill(self, loc, *kind).into_expr_err(loc)?;
                Ok(true)
            }
            (ExprRet::Single(ty), Some(ExprRet::SingleLiteral(rhs))) => {
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar.literal_cast_from_ty(ty, self).into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_var_def(
                    ctx,
                    var_decl,
                    loc,
                    lhs_paths,
                    Some(&ExprRet::Single(rhs_cvar.into())),
                )
            }
            (ExprRet::Single(ty), Some(ExprRet::Single(rhs))) => {
                println!("HERE");
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
                    is_return: false,
                    ty,
                };
                println!("var: {var:?}");
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));
                let rhs = ContextVarNode::from(*rhs);

                // fn match_assign_ret(
                //     analyzer: &mut (impl GraphLike + AnalyzerLike),
                //     ctx: ContextNode,
                //     ret: ExprRet,
                // ) {
                //     match ret {
                //         ExprRet::Single(new_lhs) | ExprRet::SingleLiteral(new_lhs) => {
                //             analyzer.add_edge(new_lhs, ctx, Edge::Context(ContextEdge::Variable));
                //         }
                //         ExprRet::Multi(inner) => inner
                //             .into_iter()
                //             .for_each(|i| match_assign_ret(analyzer, ctx, i)),
                //         ExprRet::CtxKilled(_) => {},
                //         ExprRet::Null => {},
                //     }
                // }

                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let _ = analyzer.assign(loc, lhs, rhs, ctx)?;
                    // match_assign_ret(analyzer, ctx, ret);
                    Ok(())
                })?;

                Ok(false)
            }
            (ExprRet::Single(ty), None) => {
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
                    is_return: false,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));
                Ok(false)
            }
            (l @ ExprRet::Single(_lhs), Some(ExprRet::Multi(rhs_sides))) => Ok(rhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, l, Some(expr_ret)))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), r @ Some(ExprRet::Single(_))) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, expr_ret, r))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), None) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, expr_ret, None))
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
                            self.match_var_def(ctx, var_decl, loc, lhs_expr_ret, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                } else {
                    Ok(rhs_sides
                        .iter()
                        .map(|rhs_expr_ret| {
                            self.match_var_def(ctx, var_decl, loc, lhs_paths, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                }
            }
            (_e, _f) => Err(ExprErr::Todo(
                loc,
                "Unhandled ExprRet combination in `match_var_def`".to_string(),
            )),
        }
    }

    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        if !ctx.killed_or_ret(self).unwrap() {
            let edges = ctx.live_edges(self).into_expr_err(expr.loc())?;
            if edges.is_empty() {
                self.parse_ctx_expr_inner(expr, ctx)
            } else {
                edges
                    .iter()
                    .try_for_each(|fork_ctx| self.parse_ctx_expr(expr, *fork_ctx))?;
                Ok(())
            }
        } else {
            Ok(())
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    fn parse_ctx_expr_inner(&mut self, expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        use Expression::*;
        println!(
            "ctx: {}, current stack: {:?}, \n{:?}\n",
            ctx.underlying(self).unwrap().path,
            ctx.underlying(self)
                .unwrap()
                .expr_ret_stack
                .iter()
                .map(|i| i.debug_str(self))
                .collect::<Vec<_>>(),
            expr
        );
        match expr {
            // literals
            NumberLiteral(loc, int, exp, _unit) => self.number_literal(ctx, *loc, int, exp, false),
            AddressLiteral(loc, addr) => self.address_literal(ctx, *loc, addr),
            StringLiteral(lits) => lits
                .iter()
                .try_for_each(|lit| self.string_literal(ctx, lit.loc, &lit.string)),
            BoolLiteral(loc, b) => self.bool_literal(ctx, *loc, *b),
            HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
            HexLiteral(hexes) => self.hex_literals(ctx, hexes),
            RationalNumberLiteral(loc, integer, fraction, exp, unit) => {
                self.rational_number_literal(ctx, *loc, integer, fraction, exp, unit)
            }
            Negate(_loc, expr) => match &**expr {
                NumberLiteral(loc, int, exp, _unit) => {
                    self.number_literal(ctx, *loc, int, exp, true)
                }
                HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, true),
                e => {
                    self.parse_ctx_expr(e, ctx)?;
                    self.apply_to_edges(ctx, e.loc(), &|analyzer, ctx, loc| {
                        tracing::trace!("Negate variable pop");
                        let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoRhs(loc, "No variable present to negate".to_string()))
                        };
                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        // Solidity is dumb and used to allow negation of unsigned integers.
                        // That means we have to cast this as a int256.
                        let var = rhs_paths.expect_single().into_expr_err(loc)?;

                        let zero = analyzer.add_node(Node::Concrete(Concrete::from(I256::from(0i32))));
                        let zero = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            zero.into(),
                            analyzer,
                        ).into_expr_err(loc)?;
                        let zero = analyzer.add_node(Node::ContextVar(zero));
                        let new_underlying = ContextVarNode::from(var)
                            .underlying(analyzer).into_expr_err(loc)?
                            .clone()
                            .as_cast_tmp(loc, ctx, Builtin::Int(256), analyzer).into_expr_err(loc)?;
                        let node = analyzer.add_node(Node::ContextVar(new_underlying));
                        ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));

                        ContextVarNode::from(node).cast_from(
                            &ContextVarNode::from(zero),
                            analyzer
                        ).into_expr_err(loc)?;

                        let lhs_paths = ExprRet::Single(zero);
                        analyzer.op_match(
                            ctx,
                            loc,
                            &lhs_paths,
                            &ExprRet::Single(ContextVarNode::from(node).latest_version(analyzer).into()),
                            RangeOp::Sub(true),
                            false,
                        )
                    })
                } // e => todo!("UnaryMinus unexpected rhs: {e:?}"),
            },
            UnaryPlus(_loc, e) => todo!("UnaryPlus unexpected rhs: {e:?}"),

            // Binary ops
            Power(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Exp, false)
            }
            Add(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Add(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignAdd(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Add(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Subtract(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Sub(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignSubtract(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Sub(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Multiply(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Mul(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignMultiply(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Mul(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div(false), false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div(false), true)
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
            BitwiseNot(loc, lhs_expr) => self.bit_not(*loc, lhs_expr, ctx),

            // assign
            Assign(loc, lhs_expr, rhs_expr) => self.assign_exprs(*loc, lhs_expr, rhs_expr, ctx),
            List(loc, params) => self.list(ctx, *loc, params),
            // array
            ArraySubscript(_loc, ty_expr, None) => self.array_ty(ty_expr, ctx),
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.index_into_array(*loc, ty_expr, index_expr, ctx)
            }
            ArraySlice(loc, _lhs_expr, _maybe_middle_expr, _maybe_rhs) => Err(ExprErr::Todo(
                *loc,
                "Array slicing not currently supported".to_string(),
            )),
            ArrayLiteral(loc, _) => Err(ExprErr::Todo(
                *loc,
                "Array literal not currently supported".to_string(),
            )),

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
                // TODO: update msg node
                Err(ExprErr::Todo(
                    *loc,
                    "Function call block is unsupported. We shouldn't have hit this code path"
                        .to_string(),
                ))
            }
            NamedFunctionCall(loc, func_expr, input_args) => {
                self.named_fn_call_expr(ctx, loc, func_expr, input_args)
            }
            FunctionCall(loc, func_expr, input_exprs) => {
                let updated_func_expr = match **func_expr {
                    FunctionCallBlock(_loc, ref inner_func_expr, ref call_block) => {
                        // we dont currently handle the `{value: .. gas: ..}` msg updating
                        self.add_expr_err(ExprErr::Todo(call_block.loc(), "Function call block is currently unsupported. Relevant changes on `msg` will not take affect".to_string()));
                        inner_func_expr.clone()
                    }
                    _ => func_expr.clone(),
                };

                self.fn_call_expr(ctx, loc, &updated_func_expr, input_exprs)
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
                ctx.add_var(cvar.into(), self).into_expr_err(*loc)?;
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            MemberAccess(loc, member_expr, ident) => {
                self.member_access(*loc, member_expr, ident, ctx)
            }

            Delete(loc, expr) => {
                fn delete_match(
                    ctx: ContextNode,
                    loc: &Loc,
                    analyzer: &mut (impl GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr>),
                    ret: ExprRet,
                ) {
                    match ret {
                        ExprRet::CtxKilled(kind) => {
                            let _ = ctx.kill(analyzer, *loc, kind);
                        }
                        ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                            let mut new_var =
                                analyzer.advance_var_in_ctx(cvar.into(), *loc, ctx).unwrap();
                            let res = new_var.sol_delete_range(analyzer).into_expr_err(*loc);
                            let _ = analyzer.add_if_err(res);
                        }
                        ExprRet::Multi(inner) => {
                            inner
                                .iter()
                                .for_each(|i| delete_match(ctx, loc, analyzer, i.clone()));
                        }
                        ExprRet::Null => {}
                    }
                }

                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("Delete variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Delete operation had no right hand side".to_string()))
                    };

                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    delete_match(ctx, &loc, analyzer, ret);
                    Ok(())
                })
            }

            // de/increment stuff
            PreIncrement(loc, expr) => {
                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("PreIncrement variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "PreIncrement operation had no right hand side".to_string()))
                    };

                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_in_de_crement(ctx, true, true, loc, &ret)
                })
            }
            PostIncrement(loc, expr) => {
                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("PostIncrement variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "PostIncrement operation had no right hand side".to_string()))
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_in_de_crement(ctx, false, true, loc, &ret)
                })
            }
            PreDecrement(loc, expr) => {
                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("PreDecrement variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "PreDecrement operation had no right hand side".to_string()))
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_in_de_crement(ctx, true, false, loc, &ret)
                })
            }
            PostDecrement(loc, expr) => {
                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("PostDecrement variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "PostDecrement operation had no right hand side".to_string()))
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_in_de_crement(ctx, false, false, loc, &ret)
                })
            }

            // Misc.
            Variable(ident) => self.variable(ident, ctx, None),
            Type(loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        ctx.push_expr(ExprRet::Single(*idx), self)
                            .into_expr_err(*loc)?;
                        Ok(())
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        ctx.push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(*loc)?;
                        Ok(())
                    }
                } else {
                    todo!("{ty:?}");
                    ctx.push_expr(ExprRet::Null, self).into_expr_err(*loc)?;
                    Ok(())
                }
            }
            Parenthesis(_loc, expr) => self.parse_ctx_expr(expr, ctx),
        }
    }

    fn match_in_de_crement(
        &mut self,
        ctx: ContextNode,
        pre: bool,
        increment: bool,
        loc: Loc,
        rhs: &ExprRet,
    ) -> Result<(), ExprErr> {
        match rhs {
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, *kind).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::SingleLiteral(var) => {
                let res = ContextVarNode::from(*var)
                    .try_increase_size(self)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_in_de_crement(ctx, pre, increment, loc, &ExprRet::Single(*var))
            }
            ExprRet::Single(var) => {
                let cvar = ContextVarNode::from(*var);
                let elem = Elem::from(cvar);
                let one = Elem::from(Concrete::from(U256::from(1))).cast(elem.clone());
                // if let Some(r) = cvar.range(self).into_expr_err(loc)? {
                if increment {
                    if pre {
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                        let res = new_cvar
                            .set_range_min(self, elem.clone() + one.clone())
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        let res = new_cvar.set_range_max(self, elem + one).into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        ctx.push_expr(ExprRet::Single(new_cvar.into()), self)
                            .into_expr_err(loc)?;
                        Ok(())
                    } else {
                        let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                        let res = new_cvar
                            .set_range_min(self, elem.clone() + one.clone())
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        new_cvar
                            .set_range_max(self, elem + one)
                            .into_expr_err(loc)?;
                        ctx.push_expr(ExprRet::Single(dup.into()), self)
                            .into_expr_err(loc)?;
                        Ok(())
                    }
                } else if pre {
                    let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                    let res = new_cvar
                        .set_range_min(self, elem.clone() - one.clone())
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);
                    new_cvar
                        .set_range_max(self, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(new_cvar.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                    let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                    let res = new_cvar
                        .set_range_min(self, elem.clone() - one.clone())
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);
                    new_cvar
                        .set_range_max(self, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(dup.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                // } else {
                //     panic!("No range in post-increment")
                // }
            }
            ExprRet::Multi(inner) => inner
                .iter()
                .try_for_each(|expr| self.match_in_de_crement(ctx, pre, increment, loc, expr)),
            ExprRet::Null => Ok(()),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn assign_exprs(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(rhs_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Assign operation had no right hand side".to_string()))
            };
            let rhs_paths = rhs_paths.flatten();
            if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.parse_ctx_expr(lhs_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "Assign operation had no left hand side".to_string()))
                };
                if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                analyzer.match_assign_sides(ctx, loc, &lhs_paths.flatten(), &rhs_paths)?;
                Ok(())
            })
        })
    }

    fn match_assign_sides(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (ExprRet::CtxKilled(kind), _) | (_, ExprRet::CtxKilled(kind)) => {
                ctx.kill(self, loc, *kind).into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar
                    .literal_cast_from(&lhs_cvar, self)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
                ctx.push_expr(self.assign(loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                ctx.push_expr(self.assign(loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), ExprRet::Multi(rhs_sides)) => rhs_sides
                .iter()
                .try_for_each(|expr_ret| self.match_assign_sides(ctx, loc, l, expr_ret)),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.match_assign_sides(ctx, loc, expr_ret, r))
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_assign_sides(ctx, loc, lhs_expr_ret, rhs_expr_ret)
                        },
                    )
                } else {
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.match_assign_sides(ctx, loc, lhs_paths, rhs_expr_ret)
                    })
                }
            }
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
        tracing::trace!(
            "assigning: {} to {}",
            lhs_cvar.display_name(self).unwrap(),
            rhs_cvar.display_name(self).unwrap()
        );
        let (new_lower_bound, new_upper_bound): (Elem<Concrete>, Elem<Concrete>) = (
            Elem::from(rhs_cvar.latest_version(self)),
            Elem::from(rhs_cvar.latest_version(self)),
        );

        let new_lhs = self.advance_var_in_ctx(lhs_cvar.latest_version(self), loc, ctx)?;
        if rhs_cvar.underlying(self).into_expr_err(loc)?.is_return {
            if let Some(rhs_ctx) = rhs_cvar.maybe_ctx(self) {
                self.add_edge(
                    rhs_cvar,
                    new_lhs,
                    Edge::Context(ContextEdge::ReturnAssign(
                        rhs_ctx.underlying(self).unwrap().ext_fn_call.is_some(),
                    )),
                );
            } else {
                return Err(ExprErr::GraphError(
                    loc,
                    GraphError::DetachedVariable(format!(
                        "No context for variable: {}, node idx: {}, curr ctx: {}, lhs ctx: {}",
                        rhs_cvar.display_name(self).unwrap(),
                        rhs_cvar.0,
                        ctx.path(self),
                        lhs_cvar.ctx(self).path(self)
                    )),
                ));
            }
        }
        if !lhs_cvar.ty_eq(&rhs_cvar, self).into_expr_err(loc)? {
            let cast_to_min = match lhs_cvar.range_min(self).into_expr_err(loc)? {
                Some(v) => v,
                None => {
                    return Err(ExprErr::BadRange(
                        loc,
                        format!(
                            "No range during cast? {:?}, {:?}",
                            lhs_cvar.underlying(self).unwrap(),
                            rhs_cvar.underlying(self).unwrap(),
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
                            "No range during cast? {:?}, {:?}",
                            lhs_cvar.underlying(self).unwrap(),
                            rhs_cvar.underlying(self).unwrap(),
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
        if let Some(rhs_range) = rhs_cvar.ref_range(self).into_expr_err(loc)? {
            let res = new_lhs
                .try_set_range_exclusions(self, rhs_range.exclusions.clone())
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
                    if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                        let min = r.evaled_range_min(self).into_expr_err(loc)?;
                        let max = r.evaled_range_max(self).into_expr_err(loc)?;

                        if let Some(mut rd) = min.maybe_range_dyn() {
                            rd.val.insert(Elem::from(index), Elem::from(rhs_cvar));
                            let res = next_arr
                                .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc);
                            let _ = self.add_if_err(res);
                        }

                        if let Some(mut rd) = max.maybe_range_dyn() {
                            rd.val.insert(Elem::from(index), Elem::from(rhs_cvar));
                            let res = next_arr
                                .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc);
                            let _ = self.add_if_err(res);
                        }
                    }
                }
            }
        }

        Ok(ExprRet::Single(new_lhs.into()))
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    fn advance_var_in_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<ContextVarNode, ExprErr> {
        tracing::trace!(
            "advancing variable: {}",
            cvar_node.display_name(self).into_expr_err(loc)?
        );
        if let Some(cvar) = cvar_node.next_version(self) {
            panic!(
                "Not latest version of: {}",
                cvar.display_name(self).unwrap()
            );
        }
        if let Some(child) = ctx.underlying(self).into_expr_err(loc)?.child {
            return Err(ExprErr::GraphError(
                loc,
                // GraphError::VariableUpdateInOldContext(format!(
                panic!(
                    "Variable update of {} in old context: parent: {}, child: {:#?}",
                    cvar_node.display_name(self).unwrap(),
                    ctx.path(self),
                    child
                ), //),
            ));
        }
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
        // get the old context
        let new_cvarnode;

        'a: {
            if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
                // get the previous version to remove and prevent spurious nodes
                if let Some(prev) = cvar_node.latest_version(self).previous_version(self) {
                    let prev_version = prev.underlying(self).into_expr_err(loc)?;
                    // check if there was no change between the previous version and the latest version
                    if prev_version.eq_ignore_loc(&new_cvar) && old_ctx == ctx {
                        // there was no change in the current context, just give them the current variable
                        new_cvarnode = cvar_node.into();
                        break 'a;
                    }
                }

                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
                if old_ctx != ctx {
                    ctx.add_var(new_cvarnode.into(), self).into_expr_err(loc)?;
                    self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(
                        new_cvarnode,
                        cvar_node.0,
                        Edge::Context(ContextEdge::InheritedVariable),
                    );
                } else {
                    self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
                }
            } else {
                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        }

        Ok(ContextVarNode::from(new_cvarnode))
    }

    fn advance_var_in_curr_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        tracing::trace!(
            "advancing variable: {}",
            cvar_node.display_name(self).into_expr_err(loc)?
        );
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
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));

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

    fn apply_to_edges(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        closure: &impl Fn(&mut Self, ContextNode, Loc) -> Result<(), ExprErr>,
    ) -> Result<(), ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        tracing::trace!(
            "Applying to live edges of: {}. edges: {:#?}",
            ctx.path(self),
            live_edges.iter().map(|i| i.path(self)).collect::<Vec<_>>(),
        );
        if !ctx.killed_or_ret(self).into_expr_err(loc)? {
            if ctx.underlying(self).into_expr_err(loc)?.child.is_some() {
                if live_edges.is_empty() {
                    Ok(())
                } else {
                    live_edges
                        .iter()
                        .try_for_each(|ctx| closure(self, *ctx, loc))
                }
            } else if live_edges.is_empty() {
                closure(self, ctx, loc)
            } else {
                live_edges
                    .iter()
                    .try_for_each(|ctx| closure(self, *ctx, loc))
            }
        } else {
            Ok(())
        }
    }

    fn take_from_edge<T>(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        closure: &impl Fn(&mut Self, ContextNode, Loc) -> Result<T, ExprErr>,
    ) -> Result<Vec<T>, ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        tracing::trace!(
            "Taking from live edges of: {}. edges: {:#?}",
            ctx.path(self),
            live_edges.iter().map(|i| i.path(self)).collect::<Vec<_>>(),
        );

        if live_edges.is_empty() {
            Ok(vec![closure(self, ctx, loc)?])
        } else {
            live_edges
                .iter()
                .map(|ctx| closure(self, *ctx, loc))
                .collect::<Result<Vec<T>, ExprErr>>()
        }
    }
}
