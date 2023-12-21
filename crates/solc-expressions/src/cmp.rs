use crate::{ContextBuilder, ExprErr, ExpressionParser, IntoExprErr};

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        TmpConstruction,
    },
    AnalyzerBackend, GraphError, Node, Range, SolcRange, VarType,
};

use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

impl<T> Cmp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles comparator operations, i.e: `!`
pub trait Cmp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn not(&mut self, loc: Loc, lhs_expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        self.parse_ctx_expr(lhs_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
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
            analyzer.not_inner(ctx, loc, lhs.flatten())
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn not_inner(&mut self, ctx: ContextNode, loc: Loc, lhs_expr: ExprRet) -> Result<(), ExprErr> {
        match lhs_expr {
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)?;
                ctx.push_expr(lhs_expr, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Single(lhs) | ExprRet::SingleLiteral(lhs) => {
                let lhs_cvar = ContextVarNode::from(lhs);
                tracing::trace!("not: {}", lhs_cvar.display_name(self).into_expr_err(loc)?);
                let range = self.not_eval(ctx, loc, lhs_cvar)?;
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
                    is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                    is_return: false,
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ctx.push_expr(
                    ExprRet::Single(self.add_node(Node::ContextVar(out_var))),
                    self,
                )
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
        loc: Loc,
        lhs_expr: &Expression,
        op: RangeOp,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            analyzer.parse_ctx_expr(rhs_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
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

                analyzer.parse_ctx_expr(lhs_expr, ctx)?;
                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
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
                    analyzer.cmp_inner(ctx, loc, &lhs_paths.flatten(), op, &rhs_paths)
                })
            })
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cmp_inner(
        &mut self,
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
                self.cmp_inner(ctx, loc, &ExprRet::Single(*rhs), op, rhs_paths)
            }
            (ExprRet::SingleLiteral(lhs), ExprRet::SingleLiteral(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                lhs_cvar.try_increase_size(self).into_expr_err(loc)?;
                rhs_cvar.try_increase_size(self).into_expr_err(loc)?;
                self.cmp_inner(
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
                self.cmp_inner(ctx, loc, lhs_paths, op, &ExprRet::Single(*rhs))
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
                        .range_exclusions();
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
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ctx.push_expr(
                    ExprRet::Single(self.add_node(Node::ContextVar(out_var))),
                    self,
                )
                .into_expr_err(loc)
            }
            (l @ ExprRet::Single(_lhs), ExprRet::Multi(rhs_sides)) => {
                rhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(ctx, loc, l, op, expr_ret))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => {
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.cmp_inner(ctx, loc, expr_ret, op, r))?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.cmp_inner(ctx, loc, lhs_expr_ret, op, rhs_expr_ret)
                        },
                    )?;
                    Ok(())
                } else {
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.cmp_inner(ctx, loc, lhs_paths, op, rhs_expr_ret)
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

    fn not_eval(
        &self,
        _ctx: ContextNode,
        loc: Loc,
        lhs_cvar: ContextVarNode,
    ) -> Result<SolcRange, ExprErr> {
        if let Some(lhs_range) = lhs_cvar.ref_range(self).into_expr_err(loc)? {
            let lhs_min = lhs_range.evaled_range_min(self).into_expr_err(loc)?;

            // invert
            if lhs_min.range_eq(&lhs_range.evaled_range_max(self).into_expr_err(loc)?, self) {
                let val = Elem::Expr(RangeExpr::new(
                    lhs_range.range_min().into_owned(),
                    RangeOp::Not,
                    Elem::Null,
                ));

                return Ok(SolcRange::new(val.clone(), val, lhs_range.exclusions.clone()));
            }
        }

        let min = RangeConcrete {
            val: Concrete::Bool(false),
            loc,
        };

        let max = RangeConcrete {
            val: Concrete::Bool(true),
            loc,
        };
        Ok(SolcRange::new(
            Elem::Concrete(min),
            Elem::Concrete(max),
            vec![],
        ))
    }

    fn range_eval(
        &self,
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

                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min, self) {
                            return Ok(true.into());
                        }

                        // Similarly if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        match lhs_min.range_ord(&rhs_max, self) {
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
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max, self) {
                            return Ok(true.into());
                        }

                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        match lhs_max.range_ord(&rhs_min, self) {
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
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        match lhs_max.range_ord(&rhs_min, self) {
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
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max, self) {
                            return Ok(false.into());
                        }
                    }
                    RangeOp::Gte => {
                        // if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        match lhs_min.range_ord(&rhs_max, self) {
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
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min, self) {
                            return Ok(false.into());
                        }
                    }
                    RangeOp::Eq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        if let (
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                        ) = (
                            // check lhs_min == lhs_max, ensures lhs is const
                            lhs_min.range_ord(&lhs_max, self),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min, self),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max, self),
                        ) {
                            return Ok(true.into());
                        }
                    }
                    RangeOp::Neq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        if let (
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                            Some(Ordering::Equal),
                        ) = (
                            // check lhs_min == lhs_max, ensures lhs is const
                            lhs_min.range_ord(&lhs_max, self),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min, self),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max, self),
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
