//! Trait and blanket implementation for the core parsing loop
use crate::{ExprErr, IntoExprErr};

use graph::{
    nodes::{ContextNode, ContextVarNode, ExprRet, KilledKind},
    AnalyzerBackend, ContextEdge, Edge, GraphError,
};

use solang_parser::pt::{Expression, Loc};

impl<T> ContextBuilder for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + StatementParser
{
}

mod expr;
mod stmt;
mod fn_calls;

pub use expr::*;
pub use stmt::*;
pub use fn_calls::*;

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
    fn return_match(&mut self, ctx: ContextNode, loc: &Loc, paths: &ExprRet) {
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

    /// Apply an expression or statement to all *live* edges of a context. This is used everywhere
    /// to ensure we only ever update *live* contexts. If a context has a subcontext, we *never*
    /// want to update the original context. We only ever want to operate on the latest edges.
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

    /// The inverse of [`apply_to_edges`], used only for modifiers because modifiers have extremely weird
    /// dynamics.
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
