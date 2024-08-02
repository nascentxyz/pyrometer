use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        TmpConstruction,
    },
    AnalyzerBackend, SolcRange, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> Cmp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles comparator operations, i.e: `!`
pub trait Cmp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform logical not operation
    #[tracing::instrument(level = "trace", skip_all)]
    fn not_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        lhs_expr: ExprRet,
    ) -> Result<(), ExprErr> {
        match lhs_expr {
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)?;
                ctx.push_expr(lhs_expr, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Single(lhs) | ExprRet::SingleLiteral(lhs) => {
                let lhs_cvar =
                    ContextVarNode::from(lhs).latest_version_or_inherited_in_ctx(ctx, self);
                tracing::trace!("not: {}", lhs_cvar.display_name(self).into_expr_err(loc)?);

                let elem = Elem::Expr(RangeExpr::new(
                    Elem::from(lhs_cvar),
                    RangeOp::Eq,
                    Elem::from(false),
                ));

                let bool_idx = self.builtin_or_add(Builtin::Bool);
                let ty = VarType::try_from_idx(self, bool_idx).unwrap();

                let false_node = self.add_concrete_var(ctx, Concrete::from(false), loc)?;
                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}(!{})",
                        ctx.new_tmp(self).into_expr_err(loc)?,
                        lhs_cvar.name(self).into_expr_err(loc)?,
                    ),
                    display_name: format!("!{}", lhs_cvar.display_name(self).into_expr_err(loc)?,),
                    storage: None,
                    is_tmp: true,
                    tmp_of: Some(TmpConstruction::new(
                        lhs_cvar,
                        RangeOp::Eq,
                        Some(false_node),
                    )),
                    dep_on: Some(lhs_cvar.dependent_on(self, true).into_expr_err(loc)?),
                    is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                    is_return: false,
                    ty,
                };
                let cvar = ContextVarNode::from(self.add_node(out_var));
                cvar.set_range_min(self, arena, elem.clone())
                    .into_expr_err(loc)?;
                cvar.set_range_max(self, arena, elem.clone())
                    .into_expr_err(loc)?;

                ctx.push_expr(ExprRet::Single(cvar.0.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Multi(f) => Err(ExprErr::MultiNot(
                loc,
                format!("Multiple elements in not expression: {f:?}"),
            )),
            ExprRet::Null => Err(ExprErr::NoRhs(
                loc,
                "No right hand side in `not` expression".to_string(),
            )),
        }
    }

    /// Performs a comparison operation
    #[tracing::instrument(level = "trace", skip_all)]
    fn cmp_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        lhs_paths: &ExprRet,
        op: RangeOp,
        rhs_paths: &ExprRet,
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (ExprRet::SingleLiteral(lhs), ExprRet::Single(rhs)) => {
                // ie: 5 == x
                ContextVarNode::from(*lhs)
                    .literal_cast_from(&ContextVarNode::from(*rhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(arena, ctx, loc, &ExprRet::Single(*rhs), op, rhs_paths)
            }
            (ExprRet::SingleLiteral(lhs), ExprRet::SingleLiteral(rhs)) => {
                // ie: 5 == 5
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                lhs_cvar.try_increase_size(self, arena).into_expr_err(loc)?;
                rhs_cvar.try_increase_size(self, arena).into_expr_err(loc)?;
                self.cmp_inner(
                    arena,
                    ctx,
                    loc,
                    &ExprRet::Single(lhs_cvar.into()),
                    op,
                    &ExprRet::Single(rhs_cvar.into()),
                )
            }
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                // ie: x == 5
                ContextVarNode::from(*rhs)
                    .literal_cast_from(&ContextVarNode::from(*lhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(arena, ctx, loc, lhs_paths, op, &ExprRet::Single(*rhs))
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                // ie: x == y
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                tracing::trace!(
                    "cmp: {} {op} {}",
                    lhs_cvar.display_name(self).unwrap(),
                    rhs_cvar.display_name(self).unwrap()
                );
                let range = {
                    let elem = Elem::Expr(RangeExpr::new(
                        Elem::from(lhs_cvar),
                        op,
                        Elem::from(rhs_cvar),
                    ));

                    let exclusions = lhs_cvar
                        .ref_range(self)
                        .into_expr_err(loc)?
                        .expect("No lhs range")
                        .exclusions
                        .clone();
                    SolcRange::new(elem.clone(), elem, exclusions)
                };

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}({} {} {})",
                        ctx.new_tmp(self).into_expr_err(loc)?,
                        lhs_cvar.name(self).into_expr_err(loc)?,
                        op,
                        rhs_cvar.name(self).into_expr_err(loc)?,
                    ),
                    display_name: format!(
                        "{} {op} {}",
                        lhs_cvar.display_name(self).into_expr_err(loc)?,
                        rhs_cvar.display_name(self).into_expr_err(loc)?,
                    ),
                    storage: None,
                    is_tmp: true,
                    is_symbolic: ContextVarNode::from(*lhs)
                        .is_symbolic(self)
                        .into_expr_err(loc)?
                        || ContextVarNode::from(*rhs)
                            .is_symbolic(self)
                            .into_expr_err(loc)?,
                    is_return: false,
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar))),
                    dep_on: {
                        let mut deps = lhs_cvar.dependent_on(self, true).into_expr_err(loc)?;
                        deps.extend(rhs_cvar.dependent_on(self, true).into_expr_err(loc)?);
                        Some(deps)
                    },
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ctx.push_expr(ExprRet::Single(self.add_node(out_var)), self)
                    .into_expr_err(loc)
            }
            (l @ ExprRet::Single(_lhs), ExprRet::Multi(rhs_sides)) => {
                // ie: x == [y, z] (not possible?)
                rhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(arena, ctx, loc, l, op, expr_ret))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => {
                // ie: (x, y) == z (not possible?)
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(arena, ctx, loc, expr_ret, op, r))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                // ie: (x, y) == (a, b) (not possible?)
                // ie: (x, y, z) == (a, b) (not possible?)
                if lhs_sides.len() == rhs_sides.len() {
                    // ie: (x, y) == (a, b) (not possible?)
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.cmp_inner(arena, ctx, loc, lhs_expr_ret, op, rhs_expr_ret)
                        },
                    )?;
                    Ok(())
                } else {
                    // ie: (x, y, z) == (a, b) (not possible?)
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.cmp_inner(arena, ctx, loc, lhs_paths, op, rhs_expr_ret)
                    })?;
                    Ok(())
                }
            }
            (e, f) => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled combination in `cmp`: {e:?} {f:?}"),
            )),
        }
    }
}
