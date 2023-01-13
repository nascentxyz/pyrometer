use crate::range::BoolRange;
use crate::range::BuiltinRange;
use crate::range::ElemEval;
use crate::range::RangeSize;
use crate::ExprRet;
use crate::{
    range::Op, AnalyzerLike, BuiltInNode, Builtin, ContextBuilder, ContextNode, ContextVar,
    ContextVarNode, Node, TmpConstruction, VarType,
};

use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

impl<T> Cmp for T where T: AnalyzerLike + Sized {}
pub trait Cmp: AnalyzerLike + Sized {
    fn not(&mut self, loc: Loc, lhs_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let lhs = self.parse_ctx_expr(&lhs_expr, ctx);
        self.not_inner(loc, lhs)
    }

    fn not_inner(&mut self, loc: Loc, lhs_expr: ExprRet) -> ExprRet {
        match lhs_expr {
            ExprRet::CtxKilled => lhs_expr,
            ExprRet::Single((ctx, lhs)) => {
                let lhs_cvar = ContextVarNode::from(lhs);
                let range = self.not_eval(loc, lhs_cvar);

                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!("tmp{}(!{})", lhs_cvar.name(self), ctx.new_tmp(self)),
                    display_name: format!("!{}", lhs_cvar.display_name(self),),
                    storage: None,
                    is_tmp: true,
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, Op::Not, None)),
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        Some(range),
                    ),
                };

                ExprRet::Single((ctx, self.add_node(Node::ContextVar(out_var))))
            }
            ExprRet::Multi(f) => {
                panic!("not: {:?}", f)
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
        op: Op,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(&lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx);
        self.cmp_inner(loc, &lhs_paths, op, &rhs_paths)
    }
    fn cmp_inner(&mut self, loc: Loc, lhs_paths: &ExprRet, op: Op, rhs_paths: &ExprRet) -> ExprRet {
        match (lhs_paths, rhs_paths) {
            (ExprRet::Single((ctx, lhs)), ExprRet::Single((_rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                let range = self.range_eval(lhs_cvar, rhs_cvar, op);
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
                    .into_iter()
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
                            .into_iter()
                            .zip(rhs_sides.into_iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.cmp_inner(loc, lhs_expr_ret, op, rhs_expr_ret)
                            })
                            .collect(),
                    )
                } else {
                    ExprRet::Multi(
                        rhs_sides
                            .into_iter()
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

    fn not_eval(&self, loc: Loc, lhs_cvar: ContextVarNode) -> BuiltinRange {
        if let Some(lhs_range) = lhs_cvar.range(self) {
            let lhs_min = lhs_range.range_min();

            // invert
            if lhs_min.range_eq(&lhs_range.range_max(), self) {
                if let Some(inv_lhs_min) = lhs_min.bool_elem().invert(loc) {
                    BuiltinRange::Bool(BoolRange::from(inv_lhs_min))
                } else {
                    BuiltinRange::Bool(BoolRange::default())
                }
            } else {
                BuiltinRange::Bool(BoolRange::default())
            }
        } else {
            BuiltinRange::Bool(BoolRange::default())
        }
    }

    fn range_eval(
        &self,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        op: Op,
    ) -> BuiltinRange {
        if let Some(lhs_range) = lhs_cvar.range(self) {
            if let Some(rhs_range) = rhs_cvar.range(self) {
                match op {
                    Op::Lt => {
                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // true
                        let lhs_max = lhs_range.range_max().eval(self).num_elem();
                        let rhs_min = rhs_range.range_min().eval(self).num_elem();
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return BuiltinRange::from(true);
                            }
                            _ => {}
                        }

                        // Similarly if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.range_min().eval(self).num_elem();
                        let rhs_max = rhs_range.range_max().eval(self).num_elem();
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return BuiltinRange::from(false);
                            }
                            Some(Ordering::Equal) => {
                                return BuiltinRange::from(false);
                            }
                            _ => {}
                        }
                    }
                    Op::Gt => {
                        // if lhs_min > rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.range_min().eval(self).num_elem();
                        let rhs_max = rhs_range.range_max().eval(self).num_elem();
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return BuiltinRange::from(true);
                            }
                            _ => {}
                        }

                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.range_max().eval(self).num_elem();
                        let rhs_min = rhs_range.range_min().eval(self).num_elem();
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return BuiltinRange::from(false);
                            }
                            Some(Ordering::Equal) => {
                                return BuiltinRange::from(false);
                            }
                            _ => {}
                        }
                    }
                    Op::Lte => {
                        // if lhs_max <= rhs_min, we know this cmp will evaluate to
                        // true
                        let lhs_max = lhs_range.range_max().eval(self).num_elem();
                        let rhs_min = rhs_range.range_min().eval(self).num_elem();
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return BuiltinRange::from(true);
                            }
                            Some(Ordering::Equal) => {
                                return BuiltinRange::from(true);
                            }
                            _ => {}
                        }

                        // Similarly if lhs_min > rhs_max, we know this cmp will evaluate to
                        // false
                        let lhs_min = lhs_range.range_min().eval(self).num_elem();
                        let rhs_max = rhs_range.range_max().eval(self).num_elem();
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return BuiltinRange::from(false);
                            }
                            _ => {}
                        }
                    }
                    Op::Gte => {
                        // if lhs_min >= rhs_max, we know this cmp will evaluate to
                        // true
                        let lhs_min = lhs_range.range_min().eval(self).num_elem();
                        let rhs_max = rhs_range.range_max().eval(self).num_elem();
                        match lhs_min.range_ord(&rhs_max) {
                            Some(Ordering::Greater) => {
                                return BuiltinRange::from(true);
                            }
                            Some(Ordering::Equal) => {
                                return BuiltinRange::from(true);
                            }
                            _ => {}
                        }

                        // if lhs_max < rhs_min, we know this cmp will evaluate to
                        // false
                        let lhs_max = lhs_range.range_max().eval(self).num_elem();
                        let rhs_min = rhs_range.range_min().eval(self).num_elem();
                        match lhs_max.range_ord(&rhs_min) {
                            Some(Ordering::Less) => {
                                return BuiltinRange::from(false);
                            }
                            _ => {}
                        }
                    }
                    Op::Eq => {
                        // if all elems are equal we know its true
                        // we dont know anything else
                        let lhs_min = lhs_range.range_min().eval(self).num_elem();
                        let lhs_max = lhs_range.range_max().eval(self).num_elem();
                        let rhs_min = rhs_range.range_min().eval(self).num_elem();
                        let rhs_max = rhs_range.range_max().eval(self).num_elem();
                        match (
                            // check lhs_min == lhs_max, ensures lhs is const
                            lhs_min.range_ord(&lhs_max),
                            // check lhs_min == rhs_min, checks if lhs == rhs
                            lhs_min.range_ord(&rhs_min),
                            // check rhs_min == rhs_max, ensures rhs is const
                            rhs_min.range_ord(&rhs_max),
                        ) {
                            (
                                Some(Ordering::Equal),
                                Some(Ordering::Equal),
                                Some(Ordering::Equal),
                            ) => {
                                return BuiltinRange::from(true);
                            }
                            _ => {}
                        }
                    }
                    e => unreachable!("Cmp with strange op: {:?}", e),
                }
                BuiltinRange::Bool(BoolRange::default())
            } else {
                BuiltinRange::Bool(BoolRange::default())
            }
        } else {
            BuiltinRange::Bool(BoolRange::default())
        }
    }
}
