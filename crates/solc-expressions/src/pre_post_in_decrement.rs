use crate::variable::Variable;

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::U256;
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
                let elem = Elem::from(cvar);
                let one = Elem::from(Concrete::from(U256::from(1))).cast(elem.clone());

                // if let Some(r) = cvar.range(self).into_expr_err(loc)? {
                if increment {
                    if pre {
                        let dup = cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                        dup.set_range_min(self, arena, elem.clone() + one.clone())
                            .into_expr_err(loc)?;
                        dup.set_range_max(self, arena, elem.clone() + one.clone())
                            .into_expr_err(loc)?;
                        let new_cvar = self.advance_var_in_ctx_forcible(cvar, loc, ctx, true)?;
                        new_cvar
                            .set_range_min(self, arena, elem.clone() + one.clone())
                            .into_expr_err(loc)?;
                        new_cvar
                            .set_range_max(self, arena, elem + one)
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
                        dup.set_range_min(self, arena, elem.clone())
                            .into_expr_err(loc)?;
                        dup.set_range_max(self, arena, elem.clone())
                            .into_expr_err(loc)?;
                        let new_cvar = self.advance_var_in_ctx_forcible(cvar, loc, ctx, true)?;
                        let res = new_cvar
                            .set_range_min(self, arena, elem.clone() + one.clone())
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        new_cvar
                            .set_range_max(self, arena, elem + one)
                            .into_expr_err(loc)?;
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
                    let dup = cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                    dup.set_range_min(self, arena, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    dup.set_range_max(self, arena, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    let new_cvar = self.advance_var_in_ctx_forcible(cvar, loc, ctx, true)?;
                    new_cvar
                        .set_range_min(self, arena, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    new_cvar
                        .set_range_max(self, arena, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(
                        ExprRet::Single(dup.latest_version_or_inherited_in_ctx(ctx, self).into()),
                        self,
                    )
                    .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let dup = cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                    dup.set_range_min(self, arena, elem.clone())
                        .into_expr_err(loc)?;
                    dup.set_range_max(self, arena, elem.clone())
                        .into_expr_err(loc)?;
                    let new_cvar = self.advance_var_in_ctx_forcible(cvar, loc, ctx, true)?;
                    new_cvar
                        .set_range_min(self, arena, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    new_cvar
                        .set_range_max(self, arena, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(dup.into()), self)
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
