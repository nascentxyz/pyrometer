use crate::{ContextBuilder, ExpressionParser};

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        TmpConstruction,
    },
    AnalyzerBackend, Range, SolcRange, VarType,
};
use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

impl<T> Cmp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles comparator operations, i.e: `!`
pub trait Cmp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn not(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(arena, lhs_expr, ctx)?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let Some(lhs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "Not operation had no element".to_string(),
                ));
            };

            if matches!(lhs, ExprRet::CtxKilled(_)) {
                ctx.push_expr(lhs, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.not_inner(arena, ctx, loc, lhs.flatten())
        })
    }

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
                let lhs_cvar = ContextVarNode::from(lhs);
                tracing::trace!("not: {}", lhs_cvar.display_name(self).into_expr_err(loc)?);

                let mut elem = Elem::Expr(RangeExpr::new(
                    Elem::from(lhs_cvar),
                    RangeOp::Not,
                    Elem::Null,
                ));
                let _ = elem.arenaize(self, arena);
                let mut range = SolcRange::new(elem.clone(), elem, vec![]);

                range.cache_eval(self, arena).into_expr_err(loc)?;
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
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, RangeOp::Not, None)),
                    dep_on: Some(lhs_cvar.dependent_on(self, true).into_expr_err(loc)?),
                    is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                    is_return: false,
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ctx.push_expr(ExprRet::Single(self.add_node(out_var)), self)
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

    #[tracing::instrument(level = "trace", skip_all)]
    fn cmp(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_expr: &Expression,
        op: RangeOp,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            analyzer.parse_ctx_expr(arena, rhs_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoRhs(
                        loc,
                        "Cmp operation had no right hand side".to_string(),
                    ));
                };
                let rhs_paths = rhs_paths.flatten();

                if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }

                analyzer.parse_ctx_expr(arena, lhs_expr, ctx)?;
                analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Cmp operation had no left hand side".to_string(),
                        ));
                    };

                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.cmp_inner(arena, ctx, loc, &lhs_paths.flatten(), op, &rhs_paths)
                })
            })
        })
    }

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
                ContextVarNode::from(*lhs)
                    .literal_cast_from(&ContextVarNode::from(*rhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(arena, ctx, loc, &ExprRet::Single(*rhs), op, rhs_paths)
            }
            (ExprRet::SingleLiteral(lhs), ExprRet::SingleLiteral(rhs)) => {
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
                ContextVarNode::from(*rhs)
                    .literal_cast_from(&ContextVarNode::from(*lhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(arena, ctx, loc, lhs_paths, op, &ExprRet::Single(*rhs))
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                tracing::trace!(
                    "cmp: {} {} {}",
                    lhs_cvar.display_name(self).unwrap(),
                    op.to_string(),
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
                        op.to_string(),
                        rhs_cvar.name(self).into_expr_err(loc)?,
                    ),
                    display_name: format!(
                        "{} {} {}",
                        lhs_cvar.display_name(self).into_expr_err(loc)?,
                        op.to_string(),
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
                rhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(arena, ctx, loc, l, op, expr_ret))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => {
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(arena, ctx, loc, expr_ret, op, r))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.cmp_inner(arena, ctx, loc, lhs_expr_ret, op, rhs_expr_ret)
                        },
                    )?;
                    Ok(())
                } else {
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

    // fn not_eval(
    //     &mut self,
    //     _ctx: ContextNode,
    //     loc: Loc,
    //     lhs_cvar: ContextVarNode,
    // ) -> Result<SolcRange, ExprErr> {
    //     if let Some(lhs_range) = lhs_cvar.ref_range(self).into_expr_err(loc)? {
    //         let lhs_min = lhs_range.evaled_range_min(self, arena).into_expr_err(loc)?;

    //         // invert
    //         if lhs_min.range_eq(&lhs_range.minimize(self, arena).into_expr_err(loc)?, self) {
    //             let val = Elem::Expr(RangeExpr::new(
    //                 lhs_range.range_min().into_owned(),
    //                 RangeOp::Not,
    //                 Elem::Null,
    //             ));

    //             return Ok(SolcRange::new(val.clone(), val, lhs_range.exclusions.clone()));
    //         }
    //     }

    //     let min = Elem::Concrete(RangeConcrete {
    //         val: Concrete::Bool(false),
    //         loc,
    //     }).arenaize(self);

    //     let max = Elem::Concrete(RangeConcrete {
    //         val: Concrete::Bool(true),
    //         loc,
    //     }).arenaize(self);
    //     Ok(SolcRange::new(
    //         min,
    //         max,
    //         vec![],
    //     ))
    // }

    fn range_eval(
        &self,
        arena: &mut RangeArena<Elem<Concrete>>,
        _ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        op: RangeOp,
    ) -> Result<SolcRange, GraphError> {
        if let Some(lhs_range) = lhs_cvar.ref_range(self)? {
            if let Some(rhs_range) = rhs_cvar.ref_range(self)? {
                match op {
                    RangeOp::Lt => {
                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // true

                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min, arena) {
                            return Ok(true.into());
                        }

                        // Similarly if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        match lhs_min.range_ord(&rhs_max, arena) {
                            Some(Ordering::Greater) => {
                                return Ok(false.into());
                            }
                            Some(Ordering::Equal) => {
                                return Ok(false.into());
                            }
                            _ => {}
                        }
                    }
                    RangeOp::Gt => {
                        // if lhs_min > rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max, arena) {
                            return Ok(true.into());
                        }

                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        match lhs_max.range_ord(&rhs_min, arena) {
                            Some(Ordering::Less) => {
                                return Ok(false.into());
                            }
                            Some(Ordering::Equal) => {
                                return Ok(false.into());
                            }
                            _ => {}
                        }
                    }
                    RangeOp::Lte => {
                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // true
                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        match lhs_max.range_ord(&rhs_min, arena) {
                            Some(Ordering::Less) => {
                                return Ok(true.into());
                            }
                            Some(Ordering::Equal) => {
                                return Ok(true.into());
                            }
                            _ => {}
                        }

                        // Similarly if lhs_min > rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max, arena) {
                            return Ok(false.into());
                        }
                    }
                    RangeOp::Gte => {
                        // if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        match lhs_min.range_ord(&rhs_max, arena) {
                            Some(Ordering::Greater) => {
                                return Ok(true.into());
                            }
                            Some(Ordering::Equal) => {
                                return Ok(true.into());
                            }
                            _ => {}
                        }

                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min, arena) {
                            return Ok(false.into());
                        }
                    }
                    RangeOp::Eq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        if let (
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                        ) = (
                            // check lhs_min == lhs_max, ensures lhs is const
                            lhs_min.range_ord(&lhs_max, arena),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min, arena),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max, arena),
                        ) {
                            return Ok(true.into());
                        }
                    }
                    RangeOp::Neq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self, arena)?;
                        let lhs_max = lhs_range.evaled_range_max(self, arena)?;
                        let rhs_min = rhs_range.evaled_range_min(self, arena)?;
                        let rhs_max = rhs_range.evaled_range_max(self, arena)?;
                        if let (
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                        ) = (
                            // check lhs_min == lhs_max, ensures lhs is const
                            lhs_min.range_ord(&lhs_max, arena),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min, arena),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max, arena),
                        ) {
                            return Ok(false.into());
                        }
                    }
                    e => unreachable!("Cmp with strange op: {:?}", e),
                }
                Ok(SolcRange::default_bool())
            } else {
                Ok(SolcRange::default_bool())
            }
        } else {
            Ok(SolcRange::default_bool())
        }
    }
}
