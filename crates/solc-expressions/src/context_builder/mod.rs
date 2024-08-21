//! Trait and blanket implementation for the core parsing loop
use crate::variable::Variable;
use graph::{
    elem::Elem,
    nodes::{CallFork, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, KilledKind},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> ContextBuilder for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

mod flattened;
mod test_command_runner;

pub use flattened::*;
pub use test_command_runner::*;

/// Dispatcher for building up a context of a function
pub trait ContextBuilder: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
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
        loc: Loc,
        paths: ExprRet,
        idx: usize,
    ) {
        match paths {
            ExprRet::CtxKilled(kind) => {
                let _ = ctx.kill(self, loc, kind);
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
                    .into_expr_err(loc);

                let latest =
                    ContextVarNode::from(expr).latest_version_or_inherited_in_ctx(ctx, self);

                match target_var {
                    Ok(Some(target_var)) => {
                        // perform a cast
                        tracing::trace!(
                            "casting {} to {} in {}",
                            latest.ty(self).unwrap().as_string(self).unwrap(),
                            target_var.ty(self).unwrap().as_string(self).unwrap(),
                            ctx.path(self),
                        );
                        let needs_forcible = latest.ty_eq(&target_var, self).into_expr_err(loc);
                        let needs_forcible = self.add_if_err(needs_forcible).unwrap_or(true);
                        let next = self
                            .advance_var_in_ctx_forcible(arena, latest, loc, ctx, needs_forcible)
                            .unwrap();
                        let res = next.cast_from(&target_var, self, arena).into_expr_err(loc);
                        self.add_if_err(res);
                    }
                    Ok(None) => {}
                    Err(e) => self.add_expr_err(e),
                }

                let latest = latest.latest_version_or_inherited_in_ctx(ctx, self);
                let ret = self
                    .advance_var_in_ctx_forcible(arena, latest, loc, ctx, true)
                    .unwrap();
                let path = ctx.path(self);
                let res = ret.underlying_mut(self).into_expr_err(loc);
                match res {
                    Ok(var) => {
                        tracing::trace!("Returning: {}, {}", path, var.display_name);
                        var.is_return = true;
                        if var.ty.take_range().is_some() {
                            // a return should always be a reference
                            var.ty.set_range(Elem::from(latest).into()).unwrap();
                        }
                        self.add_edge(ret, ctx, Edge::Context(ContextEdge::Return));

                        let res = ctx.add_return_node(loc, ret, self).into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                    Err(e) => self.add_expr_err(e),
                }
            }
            ExprRet::Multi(rets) => {
                rets.into_iter().enumerate().for_each(|(i, expr_ret)| {
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
        if let Some(child) = ctx.underlying(self).into_expr_err(loc)?.child {
            match child {
                CallFork::Call(call) => {
                    self.apply_to_edges(call, loc, arena, closure)?;
                }
                CallFork::Fork(w1, w2) => {
                    self.apply_to_edges(w1, loc, arena, closure)?;
                    self.apply_to_edges(w2, loc, arena, closure)?;
                }
            }
        } else if !ctx.is_ended(self).into_expr_err(loc)? {
            closure(self, arena, ctx, loc)?;
        }
        Ok(())
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
