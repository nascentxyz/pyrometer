//! Trait and blanket implementation for the core parsing loop
use graph::{
    elem::Elem,
    nodes::{Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, KilledKind},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> ContextBuilder for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + StatementParser
{
}

mod expr;
mod flattened;
mod stmt;
mod test_command_runner;

pub use expr::*;
pub use flattened::*;
pub use stmt::*;
pub use test_command_runner::*;

/// Dispatcher for building up a context of a function
pub trait ContextBuilder:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + StatementParser
{
    /// TODO: rename this. Sometimes we dont want to kill a context if we hit an error
    fn widen_if_limit_hit(&mut self, ctx: ContextNode, maybe_err: Result<(), ExprErr>) -> bool {
        match maybe_err {
            Err(ExprErr::FunctionCallBlockTodo(_, _s)) => {
                // dont kill for this one
                false
            }
            Err(e @ ExprErr::GraphError(_, GraphError::MaxStackWidthReached(..), ..)) => {
                // TODO: we should ideally peak at each if statement body and only widen variables referenced in there
                // but for now we just delete the forks, and reset all local variables
                self.add_expr_err(e);
                true
            }
            Err(e) => {
                let res = ctx
                    .kill(self, e.loc(), KilledKind::ParseError)
                    .into_expr_err(e.loc());
                let _ = self.add_if_err(res);
                self.add_expr_err(e);
                false
            }
            _ => false,
        }
    }

    /// Match on the [`ExprRet`]s of a return statement and performs the return
    fn return_match(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        paths: &ExprRet,
        idx: usize,
    ) {
        match paths {
            ExprRet::CtxKilled(kind) => {
                let _ = ctx.kill(self, *loc, *kind);
            }
            ExprRet::Single(expr) | ExprRet::SingleLiteral(expr) => {
                // construct a variable from the return type
                let target_var = ctx
                    .associated_fn(self)
                    .map(|func| {
                        let rets = func.returns(arena, self);
                        let Some(ret) = rets.get(idx) else {
                            return Ok(None)
                        };

                        ret.underlying(self)
                            .cloned()
                            .map(|underlying| {
                                ContextVar::new_from_func_ret(ctx, self, underlying).map(|var| {
                                    var.map(|var| {
                                        ContextVarNode::from(self.add_node(var))
                                    }).ok_or(GraphError::NodeConfusion("Could not construct a context variable from function return".to_string()))
                                    .map(Some)
                                }).and_then(|i| i)
                            })
                            .and_then(|i| i)
                    })
                    .and_then(|i| i)
                    .into_expr_err(*loc);

                let latest =
                    ContextVarNode::from(*expr).latest_version_or_inherited_in_ctx(ctx, self);

                match target_var {
                    Ok(Some(target_var)) => {
                        // perform a cast
                        tracing::trace!(
                            "{}: casting {:?} to {:?}",
                            ctx.path(self),
                            latest.ty(self).unwrap(),
                            target_var.ty(self).unwrap(),
                        );
                        let next = self
                            .advance_var_in_ctx_forcible(latest, *loc, ctx, true)
                            .unwrap();
                        let res = next.cast_from(&target_var, self, arena).into_expr_err(*loc);
                        self.add_if_err(res);
                    }
                    Ok(None) => {}
                    Err(e) => self.add_expr_err(e),
                }

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
                rets.iter().enumerate().for_each(|(i, expr_ret)| {
                    self.return_match(arena, ctx, loc, expr_ret, i);
                });
            }
            ExprRet::Null => {}
        }
    }

    /// Apply an expression or statement to all *live* edges of a context. This is used everywhere
    /// to ensure we only ever update *live* contexts. If a context has a subcontext, we *never*
    /// want to update the original context. We only ever want to operate on the latest edges.
    fn apply_to_edges(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
        closure: &impl Fn(
            &mut Self,
            &mut RangeArena<Elem<Concrete>>,
            ContextNode,
            Loc,
        ) -> Result<(), ExprErr>,
    ) -> Result<(), ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        // tracing::trace!(
        //     "Applying to live edges of: {}. edges: {:#?}",
        //     ctx.path(self),
        //     live_edges.iter().map(|i| i.path(self)).collect::<Vec<_>>(),
        // );
        if !ctx.killed_or_ret(self).into_expr_err(loc)? {
            if ctx.underlying(self).into_expr_err(loc)?.child.is_some() {
                if live_edges.is_empty() {
                    Ok(())
                } else {
                    live_edges
                        .iter()
                        .try_for_each(|ctx| closure(self, arena, *ctx, loc))
                }
            } else if live_edges.is_empty() {
                closure(self, arena, ctx, loc)
            } else {
                live_edges
                    .iter()
                    .try_for_each(|ctx| closure(self, arena, *ctx, loc))
            }
        } else {
            Ok(())
        }
    }

    /// The inverse of [`apply_to_edges`], used only for modifiers because modifiers have extremely weird
    /// dynamics.
    fn take_from_edge<T>(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
        closure: &impl Fn(
            &mut Self,
            &mut RangeArena<Elem<Concrete>>,
            ContextNode,
            Loc,
        ) -> Result<T, ExprErr>,
    ) -> Result<Vec<T>, ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        tracing::trace!(
            "Taking from live edges of: {}. edges: {:#?}",
            ctx.path(self),
            live_edges.iter().map(|i| i.path(self)).collect::<Vec<_>>(),
        );

        if live_edges.is_empty() {
            Ok(vec![closure(self, arena, ctx, loc)?])
        } else {
            live_edges
                .iter()
                .map(|ctx| closure(self, arena, *ctx, loc))
                .collect::<Result<Vec<T>, ExprErr>>()
        }
    }
}
