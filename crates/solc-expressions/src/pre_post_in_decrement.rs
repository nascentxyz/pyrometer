use crate::BinOp;

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use alloy_primitives::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> PrePostIncDecrement for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}
/// Handles pre and post increment and decrement
pub trait PrePostIncDecrement:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Match on the [`ExprRet`]s of a pre-or-post in/decrement and performs it
    fn match_in_de_crement(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
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
                // ie: 5++; (not valid syntax)
                ContextVarNode::from(*var)
                    .try_increase_size(self, arena)
                    .into_expr_err(loc)?;
                self.match_in_de_crement(arena, ctx, pre, increment, loc, &ExprRet::Single(*var))
            }
            ExprRet::Single(var) => {
                // ie: a++;
                let cvar = ContextVarNode::from(*var).latest_version_or_inherited_in_ctx(ctx, self);

                // if let Some(r) = cvar.range(self).into_expr_err(loc)? {
                if increment {
                    if pre {
                        let rhs = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;
                        self.op(arena, loc, cvar, rhs, ctx, RangeOp::Add(false), true)?;
                        let dup = cvar
                            .latest_version(self)
                            .as_tmp(self, ctx, loc)
                            .into_expr_err(loc)?;
                        ctx.push_expr(
                            ExprRet::Single(
                                dup.latest_version_or_inherited_in_ctx(ctx, self).into(),
                            ),
                            self,
                        )
                        .into_expr_err(loc)?;
                        Ok(())
                    } else {
                        let dup = cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                        let rhs = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;
                        self.op(arena, loc, cvar, rhs, ctx, RangeOp::Add(false), true)?;
                        ctx.push_expr(
                            ExprRet::Single(
                                dup.latest_version_or_inherited_in_ctx(ctx, self).into(),
                            ),
                            self,
                        )
                        .into_expr_err(loc)?;
                        Ok(())
                    }
                } else if pre {
                    let rhs = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;
                    self.op(arena, loc, cvar, rhs, ctx, RangeOp::Sub(false), true)?;
                    let dup = cvar
                        .latest_version(self)
                        .as_tmp(self, ctx, loc)
                        .into_expr_err(loc)?;
                    ctx.push_expr(
                        ExprRet::Single(dup.latest_version_or_inherited_in_ctx(ctx, self).into()),
                        self,
                    )
                    .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let dup = cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                    let rhs = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;
                    self.op(arena, loc, cvar, rhs, ctx, RangeOp::Sub(false), true)?;
                    ctx.push_expr(
                        ExprRet::Single(dup.latest_version_or_inherited_in_ctx(ctx, self).into()),
                        self,
                    )
                    .into_expr_err(loc)?;
                    Ok(())
                }
            }
            ExprRet::Multi(inner) => {
                // ie: (5, 5)++; (invalid syntax)
                inner.iter().try_for_each(|expr| {
                    self.match_in_de_crement(arena, ctx, pre, increment, loc, expr)
                })
            }
            ExprRet::Null => Ok(()),
        }
    }
}
