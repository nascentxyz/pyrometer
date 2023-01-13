use crate::range::BuiltinRange;
use crate::range::RangeEval;
use crate::range::RangeSize;
use crate::ExprRet;
use ethers_core::types::I256;

use crate::{
    exprs::{BinOp, Variable},
    range::Op,
    AnalyzerLike, Concrete, ConcreteNode, ContextBuilder, ContextNode, ContextVar, ContextVarNode,
    Node, TmpConstruction,
};
use solang_parser::pt::{Expression, Loc};

type RequireRangeFn = &'static dyn Fn(BuiltinRange, BuiltinRange) -> BuiltinRange;
type RequireRangeFns = (
    RequireRangeFn,
    (RequireRangeFn, RequireRangeFn),
    RequireRangeFn,
);

impl<T> Require for T where T: Variable + BinOp + Sized + AnalyzerLike {}
pub trait Require: AnalyzerLike + Variable + BinOp + Sized {
    /// Handles a require expression
    fn handle_require(&mut self, inputs: &Vec<Expression>, ctx: ContextNode) {
        match inputs.get(0).expect("No lhs input for require statement") {
            Expression::Less(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                let fns = (
                    &BuiltinRange::lt as RequireRangeFn,
                    (
                        &BuiltinRange::gte as RequireRangeFn,
                        &BuiltinRange::lte as RequireRangeFn,
                    ),
                    &BuiltinRange::gt as RequireRangeFn,
                );
                self.handle_require_inner(*loc, &lhs_paths, &rhs_paths, fns);
            }
            Expression::More(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                let fns = (
                    &BuiltinRange::gt as RequireRangeFn,
                    (
                        &BuiltinRange::lte as RequireRangeFn,
                        &BuiltinRange::gte as RequireRangeFn,
                    ),
                    &BuiltinRange::lt as RequireRangeFn,
                );

                self.handle_require_inner(*loc, &lhs_paths, &rhs_paths, fns);
            }
            Expression::MoreEqual(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                let fns = (
                    &BuiltinRange::gte as RequireRangeFn,
                    (
                        &BuiltinRange::lte as RequireRangeFn,
                        &BuiltinRange::gte as RequireRangeFn,
                    ),
                    &BuiltinRange::lte as RequireRangeFn,
                );
                self.handle_require_inner(*loc, &lhs_paths, &rhs_paths, fns);
            }
            Expression::LessEqual(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                let fns = (
                    &BuiltinRange::lte as RequireRangeFn,
                    (
                        &BuiltinRange::gte as RequireRangeFn,
                        &BuiltinRange::lte as RequireRangeFn,
                    ),
                    &BuiltinRange::gte as RequireRangeFn,
                );
                self.handle_require_inner(*loc, &lhs_paths, &rhs_paths, fns);
            }
            Expression::Variable(ident) => {
                // let boolean = self.variable(ident, ctx)[0];
                // TODO: figure out if we need to do anything here
            }
            e => unreachable!("Require expr with noncomparator: {:?}", e),
        }
    }

    fn handle_require_inner(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        fns: RequireRangeFns,
    ) {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::CtxKilled) => {}
            (ExprRet::CtxKilled, _) => {}
            (ExprRet::Single((lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, *lhs_ctx);
                let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, *lhs_ctx);
                self.require(
                    (lhs_cvar, new_lhs),
                    (rhs_cvar, new_rhs),
                    *lhs_ctx,
                    loc,
                    fns.0,
                    fns.1,
                    fns.2,
                );
                if lhs_ctx != rhs_ctx {
                    let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, *rhs_ctx);
                    let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, *rhs_ctx);
                    self.require(
                        (lhs_cvar, new_lhs),
                        (rhs_cvar, new_rhs),
                        *rhs_ctx,
                        loc,
                        fns.0,
                        fns.1,
                        fns.2,
                    );
                }
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => {
                rhs_sides
                    .into_iter()
                    .for_each(|expr_ret| self.handle_require_inner(loc, l, expr_ret, fns));
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => {
                lhs_sides
                    .iter()
                    .for_each(|expr_ret| self.handle_require_inner(loc, expr_ret, r, fns));
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.into_iter().zip(rhs_sides.into_iter()).for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.handle_require_inner(loc, lhs_expr_ret, rhs_expr_ret, fns)
                        },
                    );
                } else {
                    rhs_sides.into_iter().for_each(|rhs_expr_ret| {
                        self.handle_require_inner(loc, lhs_paths, rhs_expr_ret, fns)
                    });
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                self.handle_require_inner(loc, lhs_world1, rhs_world1, fns);
                self.handle_require_inner(loc, lhs_world1, rhs_world2, fns);
                self.handle_require_inner(loc, lhs_world2, rhs_world1, fns);
                self.handle_require_inner(loc, lhs_world2, rhs_world2, fns);
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => {
                self.handle_require_inner(loc, l, world1, fns);
                self.handle_require_inner(loc, l, world2, fns);
            }
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => {
                self.handle_require_inner(loc, m, world1, fns);
                self.handle_require_inner(loc, m, world2, fns);
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    /// Updates the range bounds for the variables passed into the require function. If the lefthand side is a temporary value,
    /// it will recursively update the range bounds for the underlying variable
    fn require(
        &mut self,
        (lhs_cvar, new_lhs): (ContextVarNode, ContextVarNode),
        (rhs_cvar, new_rhs): (ContextVarNode, ContextVarNode),
        ctx: ContextNode,
        loc: Loc,
        lhs_range_fn: RequireRangeFn,
        inversion_fns: (RequireRangeFn, RequireRangeFn),
        rhs_range_fn: RequireRangeFn,
    ) {

        let mut any_unsat = false;
        if let Some(lhs_range) = new_lhs.underlying(self).ty.range(self) {
            if let Some(rhs_range) = new_rhs.underlying(self).ty.range(self) {
                let new_lhs_range = lhs_range_fn(lhs_range.clone(), rhs_range.clone());
                new_lhs.set_range_min(self, new_lhs_range.range_min());
                new_lhs.set_range_max(self, new_lhs_range.range_max());

                let new_rhs_range = rhs_range_fn(rhs_range, lhs_range.clone());
                new_rhs.set_range_min(self, new_rhs_range.range_min());
                new_rhs.set_range_max(self, new_rhs_range.range_max());

                any_unsat |= new_lhs_range.unsat(self);
                any_unsat |= new_rhs_range.unsat(self);
                if any_unsat {
                    ctx.kill(self, loc);
                    return;
                }

                ctx.add_ctx_dep(new_lhs, self);
                ctx.add_ctx_dep(new_rhs, self);
            }
        }

        if let Some(tmp) = lhs_cvar.tmp_of(self) {
            self.range_recursion(
                tmp,
                lhs_range_fn,
                inversion_fns,
                rhs_cvar,
                ctx,
                loc,
                &mut any_unsat,
            )
        }
    }

    /// Recursively updates the range for a
    fn range_recursion(
        &mut self,
        tmp_construction: TmpConstruction,
        lhs_range_fn: RequireRangeFn,
        (flip_fn, no_flip_fn): (RequireRangeFn, RequireRangeFn),
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        any_unsat: &mut bool,
    ) {
        // handle lhs
        if !tmp_construction.lhs.is_const(self) {
            let adjusted_gt_rhs = ContextVarNode::from(
                self.op(
                    loc,
                    rhs_cvar,
                    tmp_construction.rhs.expect("No rhs in tmp_construction"),
                    ctx,
                    tmp_construction.op.inverse(),
                    false,
                )
                .expect_single()
                .1,
            );
            let new_underlying_lhs = self.advance_var_in_ctx(tmp_construction.lhs, loc, ctx);
            if let Some(lhs_range) = new_underlying_lhs.underlying(self).ty.range(self) {
                if let Some(rhs_range) = adjusted_gt_rhs.underlying(self).ty.range(self) {
                    let new_lhs_range = no_flip_fn(lhs_range, rhs_range.clone());
                    new_underlying_lhs.set_range_min(self, new_lhs_range.range_min());
                    new_underlying_lhs.set_range_max(self, new_lhs_range.range_max());

                    if new_lhs_range.unsat(self) {
                        *any_unsat = true;
                        ctx.kill(self, loc);
                        return;
                    }
                    if let Some(tmp) = new_underlying_lhs.tmp_of(self) {
                        self.range_recursion(
                            tmp,
                            lhs_range_fn,
                            (flip_fn, no_flip_fn),
                            adjusted_gt_rhs,
                            ctx,
                            loc,
                            any_unsat,
                        );
                    }
                }
            }
        }

        // handle rhs
        if let Some(rhs) = tmp_construction.rhs {
            if !rhs.is_const(self) {
                let (needs_inverse, adjusted_gt_rhs) = match tmp_construction.op {
                    Op::Sub => {
                        let concrete = ConcreteNode(
                            self.add_node(Node::Concrete(Concrete::Int(256, I256::from(-1i32))))
                                .index(),
                        );
                        let lhs_cvar = ContextVar::new_from_concrete(loc, concrete, self);
                        let tmp_lhs =
                            ContextVarNode::from(self.add_node(Node::ContextVar(lhs_cvar)));
                        let tmp_rhs = ContextVarNode::from(
                            self.op(loc, rhs_cvar, tmp_lhs, ctx, Op::Mul, false)
                                .expect_single()
                                .1,
                        );
                        let new_rhs = ContextVarNode::from(
                            self.op(
                                loc,
                                tmp_rhs,
                                tmp_construction.lhs,
                                ctx,
                                tmp_construction.op.inverse(),
                                false,
                            )
                            .expect_single()
                            .1,
                        );
                        (true, new_rhs)
                    }
                    Op::Add => {
                        let new_rhs = ContextVarNode::from(
                            self.op(
                                loc,
                                rhs_cvar,
                                tmp_construction.lhs,
                                ctx,
                                tmp_construction.op.inverse(),
                                false,
                            )
                            .expect_single()
                            .1,
                        );
                        (false, new_rhs)
                    }
                    e => panic!("here {:?}", e),
                };

                let new_underlying_rhs = self.advance_var_in_ctx(rhs, loc, ctx);
                if let Some(lhs_range) = new_underlying_rhs.underlying(self).ty.range(self) {
                    if let Some(rhs_range) = adjusted_gt_rhs.underlying(self).ty.range(self) {
                        let new_lhs_range = if needs_inverse {
                            flip_fn(lhs_range.clone(), rhs_range.clone())
                        } else {
                            no_flip_fn(lhs_range.clone(), rhs_range.clone())
                        };

                        new_underlying_rhs.set_range_min(self, new_lhs_range.range_min());
                        new_underlying_rhs.set_range_max(self, new_lhs_range.range_max());

                        if new_lhs_range.unsat(self) {
                            *any_unsat = true;
                            ctx.kill(self, loc);
                            return;
                        }
                        if let Some(tmp) = new_underlying_rhs.tmp_of(self) {
                            self.range_recursion(
                                tmp,
                                lhs_range_fn,
                                (flip_fn, no_flip_fn),
                                adjusted_gt_rhs,
                                ctx,
                                loc,
                                any_unsat,
                            );
                        }
                    }
                }
            }
        }
    }
}
