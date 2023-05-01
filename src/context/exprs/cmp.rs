use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{ContextBuilder, ExprRet};
use shared::analyzer::GraphError;
use shared::range::elem_ty::Dynamic;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::*,
    range::{
        elem::{RangeElem, RangeOp},
        elem_ty::{Elem, RangeConcrete, RangeExpr},
        Range, SolcRange,
    },
    Node,
};

use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

impl<T> Cmp for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait Cmp: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn not(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let lhs = self.parse_ctx_expr(lhs_expr, ctx)?;
        self.not_inner(loc, lhs)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn not_inner(&mut self, loc: Loc, lhs_expr: ExprRet) -> Result<ExprRet, ExprErr> {
        match lhs_expr {
            ExprRet::CtxKilled => Ok(lhs_expr),
            ExprRet::Single((ctx, lhs)) | ExprRet::SingleLiteral((ctx, lhs)) => {
                let lhs_cvar = ContextVarNode::from(lhs);

                tracing::trace!("not: {}", lhs_cvar.display_name(self).into_expr_err(loc)?);

                let range = self.not_eval(ctx, loc, lhs_cvar);

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}(!{})",
                        lhs_cvar.name(self).into_expr_err(loc)?,
                        ctx.new_tmp(self).into_expr_err(loc)?
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

                Ok(ExprRet::Single((
                    ctx,
                    self.add_node(Node::ContextVar(out_var)),
                )))
            }
            ExprRet::Multi(f) => Err(ExprErr::MultiNot(
                loc,
                format!("Multiple elements in not expression: {f:?}"),
            )),
            ExprRet::Fork(world1, world2) => Ok(ExprRet::Fork(
                Box::new(self.not_inner(loc, *world1)?),
                Box::new(self.not_inner(loc, *world2)?),
            )),
        }
    }

    fn cmp(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        op: RangeOp,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx)?.flatten();
        let lhs_paths = self.parse_ctx_expr(lhs_expr, ctx)?.flatten();
        self.cmp_inner(loc, &lhs_paths, op, &rhs_paths)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cmp_inner(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        op: RangeOp,
        rhs_paths: &ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::SingleLiteral((_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                ContextVarNode::from(*lhs)
                    .literal_cast_from(&ContextVarNode::from(*rhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(loc, &ExprRet::Single((*rhs_ctx, *rhs)), op, rhs_paths)
            }
            (ExprRet::Single((_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                ContextVarNode::from(*rhs)
                    .literal_cast_from(&ContextVarNode::from(*lhs), self)
                    .into_expr_err(loc)?;
                self.cmp_inner(loc, lhs_paths, op, &ExprRet::Single((*rhs_ctx, *rhs)))
            }
            (ExprRet::Single((ctx, lhs)), ExprRet::Single((_rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                let range = {
                    let elem = Elem::Expr(RangeExpr {
                        lhs: Box::new(Elem::Dynamic(Dynamic::new(lhs_cvar.into()))),
                        op,
                        rhs: Box::new(Elem::Dynamic(Dynamic::new(rhs_cvar.into()))),
                    });

                    let exclusions = lhs_cvar
                        .range(self)
                        .into_expr_err(loc)?
                        .expect("No lhs rnage")
                        .range_exclusions();
                    SolcRange::new(elem.clone(), elem, exclusions)
                };
                // println!(
                //     "cmp range: {range:#?},\nmin: {:?},\nmax: {:?}\nlhs_range: {:#?}\nrhs_range: {:#?}",
                //     range.evaled_range_min(self),
                //     range.evaled_range_max(self),
                //     lhs_cvar.range(self),
                //     rhs_cvar.range(self),
                // );

                tracing::trace!(
                    "cmp: {} {} {}",
                    lhs_cvar.name(self).into_expr_err(loc)?,
                    op.to_string(),
                    rhs_cvar.name(self).into_expr_err(loc)?
                );

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}({} {} {})",
                        lhs_cvar.name(self).into_expr_err(loc)?,
                        op.to_string(),
                        rhs_cvar.name(self).into_expr_err(loc)?,
                        ctx.new_tmp(self).into_expr_err(loc)?
                    ),
                    display_name: format!(
                        "{} {} {}",
                        lhs_cvar.display_name(self).unwrap(),
                        op.to_string(),
                        rhs_cvar.display_name(self).unwrap(),
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

                Ok(ExprRet::Single((
                    *ctx,
                    self.add_node(Node::ContextVar(out_var)),
                )))
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => {
                Ok(ExprRet::Multi(
                    rhs_sides
                        .iter()
                        .map(|expr_ret| self.cmp_inner(loc, l, op, expr_ret))
                        .collect::<Result<Vec<ExprRet>, ExprErr>>()?,
                ))
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => Ok(ExprRet::Multi(
                lhs_sides
                    .iter()
                    .map(|expr_ret| self.cmp_inner(loc, expr_ret, op, r))
                    .collect::<Result<Vec<ExprRet>, ExprErr>>()?,
            )),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    Ok(ExprRet::Multi(
                        lhs_sides
                            .iter()
                            .zip(rhs_sides.iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.cmp_inner(loc, lhs_expr_ret, op, rhs_expr_ret)
                            })
                            .collect::<Result<Vec<ExprRet>, ExprErr>>()?,
                    ))
                } else {
                    Ok(ExprRet::Multi(
                        rhs_sides
                            .iter()
                            .map(|rhs_expr_ret| self.cmp_inner(loc, lhs_paths, op, rhs_expr_ret))
                            .collect::<Result<Vec<ExprRet>, ExprErr>>()?,
                    ))
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                Ok(ExprRet::Fork(
                    Box::new(ExprRet::Fork(
                        Box::new(self.cmp_inner(loc, lhs_world1, op, rhs_world1)?),
                        Box::new(self.cmp_inner(loc, lhs_world1, op, rhs_world2)?),
                    )),
                    Box::new(ExprRet::Fork(
                        Box::new(self.cmp_inner(loc, lhs_world2, op, rhs_world1)?),
                        Box::new(self.cmp_inner(loc, lhs_world2, op, rhs_world2)?),
                    )),
                ))
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => Ok(ExprRet::Fork(
                Box::new(self.cmp_inner(loc, l, op, world1)?),
                Box::new(self.cmp_inner(loc, l, op, world2)?),
            )),
            (ExprRet::Fork(world1, world2), r @ ExprRet::Single(_)) => Ok(ExprRet::Fork(
                Box::new(self.cmp_inner(loc, world1, op, r)?),
                Box::new(self.cmp_inner(loc, world2, op, r)?),
            )),
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => Ok(ExprRet::Fork(
                Box::new(self.cmp_inner(loc, m, op, world1)?),
                Box::new(self.cmp_inner(loc, m, op, world2)?),
            )),
            (e, f) => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled combination in `not`: {e:?} {f:?}"),
            )),
        }
    }

    fn not_eval(&self, _ctx: ContextNode, loc: Loc, lhs_cvar: ContextVarNode) -> SolcRange {
        if let Some(lhs_range) = lhs_cvar.range(self).unwrap() {
            let lhs_min = lhs_range.evaled_range_min(self).unwrap();

            // invert
            if lhs_min.range_eq(&lhs_range.evaled_range_max(self).unwrap()) {
                let val = Elem::Expr(RangeExpr {
                    lhs: Box::new(lhs_min),
                    op: RangeOp::Not,
                    rhs: Box::new(Elem::Null),
                });

                return SolcRange::new(val.clone(), val, lhs_range.exclusions);
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
        SolcRange::new(Elem::Concrete(min), Elem::Concrete(max), vec![])
    }

    fn range_eval(
        &self,
        _ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        op: RangeOp,
    ) -> Result<SolcRange, GraphError> {
        if let Some(lhs_range) = lhs_cvar.range(self)? {
            if let Some(rhs_range) = rhs_cvar.range(self)? {
                match op {
                    RangeOp::Lt => {
                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // true

                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min) {
                            return Ok(true.into());
                        }

                        // Similarly if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        match lhs_min.range_ord(&rhs_max) {
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
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max) {
                            return Ok(true.into());
                        }

                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self)?;
                        let rhs_min = rhs_range.evaled_range_min(self)?;
                        match lhs_max.range_ord(&rhs_min) {
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
                        match lhs_max.range_ord(&rhs_min) {
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
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max) {
                            return Ok(false.into());
                        }
                    }
                    RangeOp::Gte => {
                        // if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self)?;
                        let rhs_max = rhs_range.evaled_range_max(self)?;
                        match lhs_min.range_ord(&rhs_max) {
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
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min) {
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
                            lhs_min.range_ord(&lhs_max),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max),
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
                            lhs_min.range_ord(&lhs_max),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max),
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
