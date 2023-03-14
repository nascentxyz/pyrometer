use crate::{ContextBuilder, ExprRet};
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

impl<T> Cmp for T where T: AnalyzerLike<Expr = Expression> + Sized {}
pub trait Cmp: AnalyzerLike<Expr = Expression> + Sized {
    fn not(&mut self, loc: Loc, lhs_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let lhs = self.parse_ctx_expr(lhs_expr, ctx);
        self.not_inner(loc, lhs)
    }

    fn not_inner(&mut self, loc: Loc, lhs_expr: ExprRet) -> ExprRet {
        match lhs_expr {
            ExprRet::CtxKilled => lhs_expr,
            ExprRet::Single((ctx, lhs)) | ExprRet::SingleLiteral((ctx, lhs)) => {
                let lhs_cvar = ContextVarNode::from(lhs);
                let range = self.not_eval(ctx, loc, lhs_cvar);

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!("tmp{}(!{})", lhs_cvar.name(self), ctx.new_tmp(self)),
                    display_name: format!("!{}", lhs_cvar.display_name(self),),
                    storage: None,
                    is_tmp: true,
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, RangeOp::Not, None)),
                    is_symbolic: lhs_cvar.is_symbolic(self),
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ExprRet::Single((ctx, self.add_node(Node::ContextVar(out_var))))
            }
            ExprRet::Multi(f) => {
                panic!("not: {f:?}")
            }
            ExprRet::Fork(world1, world2) => ExprRet::Fork(
                Box::new(self.not_inner(loc, *world1)),
                Box::new(self.not_inner(loc, *world2)),
            ),
        }
    }

    fn cmp(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        op: RangeOp,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx);
        self.cmp_inner(loc, &lhs_paths, op, &rhs_paths)
    }

    fn cmp_inner(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        op: RangeOp,
        rhs_paths: &ExprRet,
    ) -> ExprRet {
        match (lhs_paths, rhs_paths) {
            (ExprRet::SingleLiteral((_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                ContextVarNode::from(*lhs).cast_from(&ContextVarNode::from(*rhs), self);
                self.cmp_inner(loc, &ExprRet::Single((*rhs_ctx, *rhs)), op, rhs_paths)
            }
            (ExprRet::Single((_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                ContextVarNode::from(*rhs).cast_from(&ContextVarNode::from(*lhs), self);
                self.cmp_inner(loc, lhs_paths, op, &ExprRet::Single((*rhs_ctx, *rhs)))
            }
            (ExprRet::Single((ctx, lhs)), ExprRet::Single((_rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                let range = {
                    let elem = Elem::Expr(RangeExpr {
                        lhs: Box::new(Elem::Dynamic(Dynamic::new(lhs_cvar.into(), loc))),
                        op,
                        rhs: Box::new(Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc))),
                    });

                    let exclusions = lhs_cvar
                        .range(self)
                        .expect("No lhs rnage")
                        .range_exclusions();
                    SolcRange {
                        min: elem.clone(),
                        max: elem,
                        exclusions,
                    }
                };

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}({} {} {})",
                        lhs_cvar.name(self),
                        op.to_string(),
                        rhs_cvar.name(self),
                        ctx.new_tmp(self)
                    ),
                    display_name: format!(
                        "{} {} {}",
                        lhs_cvar.display_name(self),
                        op.to_string(),
                        rhs_cvar.display_name(self),
                    ),
                    storage: None,
                    is_tmp: true,
                    is_symbolic: ContextVarNode::from(*lhs).is_symbolic(self)
                        || ContextVarNode::from(*rhs).is_symbolic(self),
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar))),
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ExprRet::Single((*ctx, self.add_node(Node::ContextVar(out_var))))
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => ExprRet::Multi(
                rhs_sides
                    .iter()
                    .map(|expr_ret| self.cmp_inner(loc, l, op, expr_ret))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => ExprRet::Multi(
                lhs_sides
                    .iter()
                    .map(|expr_ret| self.cmp_inner(loc, expr_ret, op, r))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    ExprRet::Multi(
                        lhs_sides
                            .iter()
                            .zip(rhs_sides.iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.cmp_inner(loc, lhs_expr_ret, op, rhs_expr_ret)
                            })
                            .collect(),
                    )
                } else {
                    ExprRet::Multi(
                        rhs_sides
                            .iter()
                            .map(|rhs_expr_ret| self.cmp_inner(loc, lhs_paths, op, rhs_expr_ret))
                            .collect(),
                    )
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                ExprRet::Fork(
                    Box::new(ExprRet::Fork(
                        Box::new(self.cmp_inner(loc, lhs_world1, op, rhs_world1)),
                        Box::new(self.cmp_inner(loc, lhs_world1, op, rhs_world2)),
                    )),
                    Box::new(ExprRet::Fork(
                        Box::new(self.cmp_inner(loc, lhs_world2, op, rhs_world1)),
                        Box::new(self.cmp_inner(loc, lhs_world2, op, rhs_world2)),
                    )),
                )
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.cmp_inner(loc, l, op, world1)),
                Box::new(self.cmp_inner(loc, l, op, world2)),
            ),
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.cmp_inner(loc, m, op, world1)),
                Box::new(self.cmp_inner(loc, m, op, world2)),
            ),
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    fn not_eval(&self, _ctx: ContextNode, loc: Loc, lhs_cvar: ContextVarNode) -> SolcRange {
        if let Some(lhs_range) = lhs_cvar.range(self) {
            let lhs_min = lhs_range.evaled_range_min(self);

            // invert
            if lhs_min.range_eq(&lhs_range.evaled_range_max(self)) {
                let val = Elem::Expr(RangeExpr {
                    lhs: Box::new(lhs_min),
                    op: RangeOp::Not,
                    rhs: Box::new(Elem::Null),
                });

                return SolcRange {
                    min: val.clone(),
                    max: val,
                    exclusions: lhs_range.exclusions,
                };
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
        SolcRange {
            min: Elem::Concrete(min),
            max: Elem::Concrete(max),
            exclusions: vec![],
        }
    }

    fn range_eval(
        &self,
        _ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        op: RangeOp,
    ) -> SolcRange {
        if let Some(lhs_range) = lhs_cvar.range(self) {
            if let Some(rhs_range) = rhs_cvar.range(self) {
                match op {
                    RangeOp::Lt => {
                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // true

                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min) {
                            return true.into();
                        }

                        // Similarly if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return false.into();
                            }
                            Some(Ordering::Equal) => {
                                return false.into();
                            }
                            _ => {}
                        }
                    }
                    RangeOp::Gt => {
                        // if lhs_min > rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max) {
                            return true.into();
                        }

                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return false.into();
                            }
                            Some(Ordering::Equal) => {
                                return false.into();
                            }
                            _ => {}
                        }
                    }
                    RangeOp::Lte => {
                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // true
                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return true.into();
                            }
                            Some(Ordering::Equal) => {
                                return true.into();
                            }
                            _ => {}
                        }

                        // Similarly if lhs_min > rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
                        if let Some(Ordering::Greater) = lhs_min.range_ord(&rhs_max) {
                            return false.into();
                        }
                    }
                    RangeOp::Gte => {
                        // if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return true.into();
                            }
                            Some(Ordering::Equal) => {
                                return true.into();
                            }
                            _ => {}
                        }

                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        if let Some(Ordering::Less) = lhs_max.range_ord(&rhs_min) {
                            return false.into();
                        }
                    }
                    RangeOp::Eq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
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
                            return true.into();
                        }
                    }
                    RangeOp::Neq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.evaled_range_min(self);
                        let lhs_max = lhs_range.evaled_range_max(self);
                        let rhs_min = rhs_range.evaled_range_min(self);
                        let rhs_max = rhs_range.evaled_range_max(self);
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
                            return false.into();
                        }
                    }
                    e => unreachable!("Cmp with strange op: {:?}", e),
                }
                SolcRange::default_bool()
            } else {
                SolcRange::default_bool()
            }
        } else {
            SolcRange::default_bool()
        }
    }
}
