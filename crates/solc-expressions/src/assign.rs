use crate::variable::Variable;

use graph::{
    elem::{Elem, RangeElem},
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};

use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};
use solang_parser::pt::{Expression, Loc};

impl<T> Assign for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles assignments
pub trait Assign: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Match on the [`ExprRet`]s of an assignment expression
    fn match_assign_sides(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
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
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                ctx.push_expr(self.assign(arena, loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                ctx.push_expr(self.assign(arena, loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), ExprRet::Multi(rhs_sides)) => rhs_sides
                .iter()
                .try_for_each(|expr_ret| self.match_assign_sides(arena, ctx, loc, l, expr_ret)),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.match_assign_sides(arena, ctx, loc, expr_ret, r))
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_assign_sides(arena, ctx, loc, lhs_expr_ret, rhs_expr_ret)
                        },
                    )
                } else {
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.match_assign_sides(arena, ctx, loc, lhs_paths, rhs_expr_ret)
                    })
                }
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    /// Perform an assignment
    #[tracing::instrument(level = "trace", skip_all)]
    fn assign(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "assigning: {} to {}",
            rhs_cvar.display_name(self).unwrap(),
            lhs_cvar.display_name(self).unwrap(),
        );

        rhs_cvar
            .cast_from(&lhs_cvar, self, arena)
            .into_expr_err(loc)?;

        let (new_lower_bound, new_upper_bound) = (
            Elem::from(rhs_cvar.latest_version_or_inherited_in_ctx(ctx, self)),
            Elem::from(rhs_cvar.latest_version_or_inherited_in_ctx(ctx, self)),
        );

        let needs_forcible = new_lower_bound
            .depends_on(lhs_cvar, &mut vec![], self, arena)
            .into_expr_err(loc)?
            || new_upper_bound
                .depends_on(lhs_cvar, &mut vec![], self, arena)
                .into_expr_err(loc)?;

        let new_lhs = if needs_forcible {
            self.advance_var_in_ctx_forcible(
                lhs_cvar.latest_version_or_inherited_in_ctx(ctx, self),
                loc,
                ctx,
                true,
            )?
        } else {
            self.advance_var_in_ctx(
                lhs_cvar.latest_version_or_inherited_in_ctx(ctx, self),
                loc,
                ctx,
            )?
        };

        new_lhs.underlying_mut(self).into_expr_err(loc)?.tmp_of =
            rhs_cvar.tmp_of(self).into_expr_err(loc)?;

        if let Some(ref mut dep_on) = new_lhs.underlying_mut(self).into_expr_err(loc)?.dep_on {
            dep_on.push(rhs_cvar)
        } else {
            new_lhs.set_dependent_on(self).into_expr_err(loc)?;
        }

        if lhs_cvar.is_storage(self).into_expr_err(loc)? {
            self.add_edge(new_lhs, rhs_cvar, Edge::Context(ContextEdge::StorageWrite));
        }

        if rhs_cvar.underlying(self).into_expr_err(loc)?.is_return {
            if let Some(rhs_ctx) = rhs_cvar.maybe_ctx(self) {
                self.add_edge(
                    rhs_cvar,
                    new_lhs,
                    Edge::Context(ContextEdge::ReturnAssign(
                        rhs_ctx.underlying(self).unwrap().is_ext_fn_call(),
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

            let _ = new_lhs.try_set_range_min(self, arena, new_lower_bound.cast(cast_to_min));
            let _ = new_lhs.try_set_range_max(self, arena, new_upper_bound.cast(cast_to_max));
        } else {
            let _ = new_lhs.try_set_range_min(self, arena, new_lower_bound);
            let _ = new_lhs.try_set_range_max(self, arena, new_upper_bound);
        }
        if let Some(rhs_range) = rhs_cvar.ref_range(self).into_expr_err(loc)? {
            let res = new_lhs
                .try_set_range_exclusions(self, rhs_range.exclusions.clone())
                .into_expr_err(loc);
            let _ = self.add_if_err(res);
        }

        // advance the rhs variable to avoid recursion issues
        self.advance_var_in_ctx_forcible(
            rhs_cvar.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
            ctx,
            true,
        )?;
        Ok(ExprRet::Single(new_lhs.into()))
    }
}
