use crate::variable::Variable;
use graph::nodes::SubContextKind;

use graph::{
    elem::Elem,
    nodes::{Concrete, Context, ContextNode},
    AnalyzerBackend, GraphBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> Looper for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}

/// Dealing with loops
pub trait Looper:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Resets all variables referenced in the loop because we don't elegantly handle loops
    fn reset_vars(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        parent_ctx: ContextNode,
        loop_ctx: ContextNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        let subctx_kind = SubContextKind::new_fn_ret(loop_ctx, parent_ctx);
        let ret_ctx = Context::add_subctx(
            subctx_kind,
            loc,
            self,
            None,
            parent_ctx.contract_id(self).unwrap(),
            true,
        )
        .into_expr_err(loc)?;
        loop_ctx.set_child_call(ret_ctx, self).into_expr_err(loc)?;

        let vars = loop_ctx.local_vars(self).clone();
        vars.iter().try_for_each(|(name, var)| {
            // widen to max range
            if let Some(inheritor_var) = parent_ctx
                .var_by_name_or_recurse(self, name)
                .into_expr_err(loc)?
            {
                let inheritor_var =
                    inheritor_var.latest_version_or_inherited_in_ctx(loop_ctx, self);
                if let Some(r) = var
                    .underlying(self)
                    .unwrap()
                    .ty
                    .default_range(self)
                    .into_expr_err(loc)?
                {
                    let new_inheritor_var = self.advance_var_in_ctx(
                        arena,
                        inheritor_var.latest_version_or_inherited_in_ctx(ret_ctx, self),
                        loc,
                        ret_ctx,
                    )?;
                    new_inheritor_var
                        .set_range_min(self, arena, r.min)
                        .into_expr_err(loc)?;
                    new_inheritor_var
                        .set_range_max(self, arena, r.max)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    Ok(())
                }
            } else if var.is_storage(self).into_expr_err(loc)? {
                if let Some(r) = var
                    .underlying(self)
                    .unwrap()
                    .ty
                    .default_range(self)
                    .into_expr_err(loc)?
                {
                    let new_inheritor_var =
                        self.advance_var_in_ctx(arena, var.latest_version(self), loc, ret_ctx)?;
                    new_inheritor_var
                        .set_range_min(self, arena, r.min)
                        .into_expr_err(loc)?;
                    new_inheritor_var
                        .set_range_max(self, arena, r.max)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    Ok(())
                }
            } else {
                Ok(())
            }
        })
    }
}
