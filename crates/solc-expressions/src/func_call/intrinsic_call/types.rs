use crate::variable::Variable;
use crate::ListAccess;

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, TyNode,
    },
    AnalyzerBackend, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> TypesCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling type-based intrinsic functions, like `wrap`
pub trait TypesCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a type-based intrinsic function call, like `wrap`
    fn types_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match func_name {
            "type" => {
                let mut inputs = inputs.as_vec();
                ctx.push_expr(inputs.swap_remove(0), self)
                    .into_expr_err(loc)
            }
            "wrap" => {
                inputs.expect_length(2).into_expr_err(loc)?;
                let ret = inputs.as_vec();
                let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                let var = ContextVar::new_from_ty(loc, TyNode::from(wrapping_ty), ctx, self)
                    .into_expr_err(loc)?;
                let to_be_wrapped = ret[1].expect_single().into_expr_err(loc)?;
                let cvar = ContextVarNode::from(self.add_node(var));
                let next = self.advance_var_in_ctx(cvar, loc, ctx)?;
                let expr = Elem::Expr(RangeExpr::new(
                    Elem::from(to_be_wrapped),
                    RangeOp::Cast,
                    Elem::from(cvar),
                ));
                next.set_range_min(self, arena, expr.clone())
                    .into_expr_err(loc)?;
                next.set_range_max(self, arena, expr).into_expr_err(loc)?;
                ctx.push_expr(ExprRet::Single(cvar.into()), self)
                    .into_expr_err(loc)
            }
            "unwrap" => {
                inputs.expect_length(2).into_expr_err(loc)?;
                let ret = inputs.as_vec();
                let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                let mut var = ContextVar::new_from_builtin(
                    loc,
                    BuiltInNode::from(
                        TyNode::from(wrapping_ty)
                            .underlying(self)
                            .into_expr_err(loc)?
                            .ty,
                    ),
                    self,
                )
                .into_expr_err(loc)?;
                let to_be_unwrapped = ret[1].expect_single().into_expr_err(loc)?;
                var.display_name = format!(
                    "{}.unwrap({})",
                    TyNode::from(wrapping_ty).name(self).into_expr_err(loc)?,
                    ContextVarNode::from(to_be_unwrapped)
                        .display_name(self)
                        .into_expr_err(loc)?
                );

                let cvar = ContextVarNode::from(self.add_node(var));
                cvar.set_range_min(self, arena, Elem::from(to_be_unwrapped))
                    .into_expr_err(loc)?;
                cvar.set_range_max(self, arena, Elem::from(to_be_unwrapped))
                    .into_expr_err(loc)?;
                let next = self.advance_var_in_ctx(cvar, loc, ctx)?;
                let expr = Elem::Expr(RangeExpr::new(
                    Elem::from(to_be_unwrapped),
                    RangeOp::Cast,
                    Elem::from(cvar),
                ));
                next.set_range_min(self, arena, expr.clone())
                    .into_expr_err(loc)?;
                next.set_range_max(self, arena, expr).into_expr_err(loc)?;
                ctx.push_expr(ExprRet::Single(cvar.into()), self)
                    .into_expr_err(loc)
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin types function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }

    /// Perform a cast of a type
    fn cast_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        var_ty: VarType,
        ty: &Builtin,
        ret: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Null => Ok(()),
            ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                let cvar = ContextVarNode::from(cvar);
                let new_var = cvar
                    .as_cast_tmp(loc, ctx, ty.clone(), self)
                    .into_expr_err(loc)?;

                let maybe_new_range = cvar.cast_exprs(&var_ty, self, arena).into_expr_err(loc)?;
                new_var.underlying_mut(self).into_expr_err(loc)?.ty = var_ty;

                if let Some((new_min, new_max)) = maybe_new_range {
                    new_var
                        .set_range_min(self, arena, new_min)
                        .into_expr_err(loc)?;
                    new_var
                        .set_range_max(self, arena, new_max)
                        .into_expr_err(loc)?;
                }

                if cvar.needs_length(self).into_expr_err(loc)? {
                    // input is indexable. get the length attribute, create a new length for the casted type
                    let _ = self.get_length(arena, ctx, new_var.latest_version(self), true, loc)?;
                }

                ctx.push_expr(ExprRet::Single(new_var.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Multi(inner) => inner
                .into_iter()
                .try_for_each(|i| self.cast_inner(arena, ctx, var_ty.clone(), ty, i, loc)),
        }
    }
}
