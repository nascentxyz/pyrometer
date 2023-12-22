use crate::{
    context_builder::ContextBuilder, variable::Variable, ExprErr, ExpressionParser, IntoExprErr,
};

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend,
};

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
    /// Handle a preincrement
    fn pre_increment(
        &mut self,
        expr: &Expression,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            tracing::trace!("PreIncrement variable pop");
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "PreIncrement operation had no right hand side".to_string(),
                ));
            };

            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_in_de_crement(ctx, true, true, loc, &ret)
        })
    }

    /// Handle a postincrement
    fn post_increment(
        &mut self,
        expr: &Expression,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            tracing::trace!("PostIncrement variable pop");
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "PostIncrement operation had no right hand side".to_string(),
                ));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_in_de_crement(ctx, false, true, loc, &ret)
        })
    }

    /// Handle a predecrement
    fn pre_decrement(
        &mut self,
        expr: &Expression,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            tracing::trace!("PreDecrement variable pop");
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "PreDecrement operation had no right hand side".to_string(),
                ));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_in_de_crement(ctx, true, false, loc, &ret)
        })
    }

    /// Handle a postdecrement
    fn post_decrement(
        &mut self,
        expr: &Expression,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            tracing::trace!("PostDecrement variable pop");
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "PostDecrement operation had no right hand side".to_string(),
                ));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_in_de_crement(ctx, false, false, loc, &ret)
        })
    }

    /// Match on the [`ExprRet`]s of a pre-or-post in/decrement and performs it
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
                ContextVarNode::from(*var)
                    .try_increase_size(self)
                    .into_expr_err(loc)?;
                self.match_in_de_crement(ctx, pre, increment, loc, &ExprRet::Single(*var))
            }
            ExprRet::Single(var) => {
                let cvar = ContextVarNode::from(*var).latest_version(self);
                let elem = Elem::from(cvar);
                let one = Elem::from(Concrete::from(U256::from(1))).cast(elem.clone());

                // if let Some(r) = cvar.range(self).into_expr_err(loc)? {
                if increment {
                    if pre {
                        let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                        dup.set_range_min(self, elem.clone() + one.clone());
                        dup.set_range_max(self, elem.clone() + one.clone());
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                        new_cvar
                            .set_range_min(self, elem.clone() + one.clone())
                            .into_expr_err(loc)?;
                        new_cvar
                            .set_range_max(self, elem + one)
                            .into_expr_err(loc)?;
                        ctx.push_expr(ExprRet::Single(dup.latest_version(self).into()), self)
                            .into_expr_err(loc)?;
                        Ok(())
                    } else {
                        let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                        dup.set_range_min(self, elem.clone());
                        dup.set_range_max(self, elem.clone());
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                        let res = new_cvar
                            .set_range_min(self, elem.clone() + one.clone())
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        new_cvar
                            .set_range_max(self, elem + one)
                            .into_expr_err(loc)?;
                        ctx.push_expr(ExprRet::Single(dup.latest_version(self).into()), self)
                            .into_expr_err(loc)?;
                        Ok(())
                    }
                } else if pre {
                    let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                    dup.set_range_min(self, elem.clone() - one.clone());
                    dup.set_range_max(self, elem.clone() - one.clone());
                    let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                    new_cvar
                        .set_range_min(self, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    new_cvar
                        .set_range_max(self, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(dup.latest_version(self).into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let dup = cvar.as_tmp(loc, ctx, self).into_expr_err(loc)?;
                    dup.set_range_min(self, elem.clone());
                    dup.set_range_max(self, elem.clone());
                    let new_cvar = self.advance_var_in_ctx(cvar, loc, ctx)?;
                    new_cvar
                        .set_range_min(self, elem.clone() - one.clone())
                        .into_expr_err(loc)?;
                    new_cvar
                        .set_range_max(self, elem - one)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(dup.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
            }
            ExprRet::Multi(inner) => inner
                .iter()
                .try_for_each(|expr| self.match_in_de_crement(ctx, pre, increment, loc, expr)),
            ExprRet::Null => Ok(()),
        }
    }
}
