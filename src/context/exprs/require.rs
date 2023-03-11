use crate::context::exprs::cmp::Cmp;
use crate::{
    exprs::{BinOp, Variable},
    AnalyzerLike, Concrete, ConcreteNode, ContextBuilder, ExprRet, Node,
};
use shared::{
    context::*,
    nodes::{BuiltInNode, Builtin, VarType},
    range::{
        elem::{RangeElem, RangeOp},
        elem_ty::{Dynamic, Elem, RangeConcrete},
        Range, RangeEval, SolcRange,
    },
    Edge,
};

use ethers_core::types::{I256, U256};
use solang_parser::pt::{Expression, Loc};

impl<T> Require for T where T: Variable + BinOp + Sized + AnalyzerLike {}
pub trait Require: AnalyzerLike + Variable + BinOp + Sized {
    /// Handles a require expression
    fn handle_require(&mut self, inputs: &[Expression], ctx: ContextNode) {
        match inputs.get(0).expect("No lhs input for require statement") {
            Expression::Equal(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);

                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                );
            }
            Expression::NotEqual(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Neq,
                    RangeOp::Eq,
                    (RangeOp::Eq, RangeOp::Neq),
                );
            }
            Expression::Less(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Lt,
                    RangeOp::Gt,
                    (RangeOp::Gte, RangeOp::Lte),
                );
            }
            Expression::More(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Gt,
                    RangeOp::Lt,
                    (RangeOp::Lte, RangeOp::Gte),
                );
            }
            Expression::MoreEqual(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Gte,
                    RangeOp::Lte,
                    (RangeOp::Lte, RangeOp::Gte),
                );
            }
            Expression::LessEqual(loc, lhs, rhs) => {
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Lte,
                    RangeOp::Gte,
                    (RangeOp::Gte, RangeOp::Lte),
                );
            }
            Expression::Variable(ident) => {
                let lhs_paths = self.variable(ident, ctx);
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true =
                    Node::ContextVar(ContextVar::new_from_concrete(Loc::Implicit, cnode, self));
                let rhs_paths =
                    ExprRet::Single((ctx, ContextVarNode::from(self.add_node(tmp_true)).into()));
                self.handle_require_inner(
                    ident.loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                );
            }
            Expression::Not(loc, lhs) => {
                // println!("was not in require");
                let lhs_paths = self.parse_ctx_expr(lhs, ctx);
                let cnode =
                    ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(false))));
                let tmp_false =
                    Node::ContextVar(ContextVar::new_from_concrete(Loc::Implicit, cnode, self));
                let rhs_paths =
                    ExprRet::Single((ctx, ContextVarNode::from(self.add_node(tmp_false)).into()));
                // println!("{:?} {:?}", lhs_paths, rhs_paths);
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                );
            }
            Expression::And(loc, lhs, rhs) => {
                // println!("was not in require");
                let lhs_paths = self.cmp(*loc, lhs, RangeOp::Or, rhs, ctx);
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true =
                    Node::ContextVar(ContextVar::new_from_concrete(Loc::Implicit, cnode, self));
                let node = self.add_node(tmp_true);
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                let rhs_paths = ExprRet::Single((ctx, node));

                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                );
            }
            Expression::Or(loc, lhs, rhs) => {
                // println!("was not in require");
                let lhs_paths = self.cmp(*loc, lhs, RangeOp::Or, rhs, ctx);
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true =
                    Node::ContextVar(ContextVar::new_from_concrete(Loc::Implicit, cnode, self));
                let node = self.add_node(tmp_true);
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                let rhs_paths = ExprRet::Single((ctx, node));
                self.handle_require_inner(
                    *loc,
                    &lhs_paths,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                );
            }
            e => unreachable!("Require expr with noncomparator: {:?}", e),
        }
    }

    fn handle_require_inner(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        op: RangeOp,
        rhs_op: RangeOp,
        recursion_ops: (RangeOp, RangeOp),
        // fns: EitherRangeFn,
    ) {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::CtxKilled) => {}
            (ExprRet::CtxKilled, _) => {}
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                ContextVarNode::from(*rhs).cast_from(&ContextVarNode::from(*lhs), self);
                self.handle_require_inner(
                    loc,
                    lhs_paths,
                    &ExprRet::Single((*rhs_ctx, *rhs)),
                    op,
                    rhs_op,
                    recursion_ops,
                )
            }
            (ExprRet::Single((lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs);
                let rhs_cvar = ContextVarNode::from(*rhs);
                let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, *lhs_ctx);
                let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, *lhs_ctx);

                self.require(new_lhs, new_rhs, *lhs_ctx, loc, op, rhs_op, recursion_ops);
                if lhs_ctx != rhs_ctx {
                    let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, *rhs_ctx);
                    let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, *rhs_ctx);
                    self.require(new_lhs, new_rhs, *rhs_ctx, loc, op, rhs_op, recursion_ops);
                }
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => {
                rhs_sides.iter().for_each(|expr_ret| {
                    self.handle_require_inner(loc, l, expr_ret, op, rhs_op, recursion_ops)
                });
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => {
                lhs_sides.iter().for_each(|expr_ret| {
                    self.handle_require_inner(loc, expr_ret, r, op, rhs_op, recursion_ops)
                });
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.handle_require_inner(
                                loc,
                                lhs_expr_ret,
                                rhs_expr_ret,
                                op,
                                rhs_op,
                                recursion_ops,
                            )
                        },
                    );
                } else {
                    rhs_sides.iter().for_each(|rhs_expr_ret| {
                        self.handle_require_inner(
                            loc,
                            lhs_paths,
                            rhs_expr_ret,
                            op,
                            rhs_op,
                            recursion_ops,
                        )
                    });
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                self.handle_require_inner(loc, lhs_world1, rhs_world1, op, rhs_op, recursion_ops);
                self.handle_require_inner(loc, lhs_world1, rhs_world2, op, rhs_op, recursion_ops);
                self.handle_require_inner(loc, lhs_world2, rhs_world1, op, rhs_op, recursion_ops);
                self.handle_require_inner(loc, lhs_world2, rhs_world2, op, rhs_op, recursion_ops);
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => {
                self.handle_require_inner(loc, l, world1, op, rhs_op, recursion_ops);
                self.handle_require_inner(loc, l, world2, op, rhs_op, recursion_ops);
            }
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => {
                self.handle_require_inner(loc, m, world1, op, rhs_op, recursion_ops);
                self.handle_require_inner(loc, m, world2, op, rhs_op, recursion_ops);
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    /// Updates the range bounds for the variables passed into the require function. If the lefthand side is a temporary value,
    /// it will recursively update the range bounds for the underlying variable
    #[allow(clippy::too_many_arguments)]
    fn require(
        &mut self,
        new_lhs: ContextVarNode,
        new_rhs: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        op: RangeOp,
        rhs_op: RangeOp,
        recursion_ops: (RangeOp, RangeOp),
    ) -> Option<ContextVarNode> {
        let mut any_unsat = false;
        let mut tmp_cvar = None;
        if let Some(mut lhs_range) = new_lhs.underlying(self).ty.range(self) {
            let lhs_range_fn = SolcRange::dyn_fn_from_op(op);
            lhs_range.update_deps(ctx, self);
            let new_lhs_range = lhs_range_fn(lhs_range.clone(), new_rhs, loc);

            if matches!(op, RangeOp::Neq) {
                let exclusion =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));
                let excl_min = exclusion.minimize(self);
                let excl_max = exclusion.maximize(self);
                if let Some(std::cmp::Ordering::Equal) = excl_min.range_ord(&excl_max) {
                    // min and max are equal
                    if let Some(std::cmp::Ordering::Equal) =
                        lhs_range.evaled_range_min(self).range_ord(&excl_min)
                    {
                        // mins are equivalent, add 1
                        let min = lhs_range
                            .evaled_range_min(self)
                            .maybe_concrete()
                            .expect("Was not concrete");
                        let one =
                            Concrete::one(&min.val).expect("Cannot increment range elem by one");
                        let min = lhs_range.range_min() + Elem::from(one);
                        new_lhs.set_range_min(self, min);
                    } else {
                        lhs_range.exclusions.push(exclusion);
                        new_lhs.set_range_exclusions(self, lhs_range.exclusions);
                    }
                } else {
                    lhs_range.exclusions.push(exclusion);
                    new_lhs.set_range_exclusions(self, lhs_range.exclusions);
                }
            }

            if let Some(mut rhs_range) = new_rhs.range(self) {
                rhs_range.update_deps(ctx, self);
                if new_lhs.is_const(self) && !new_rhs.is_const(self) {
                    let rhs_range_fn = SolcRange::dyn_fn_from_op(rhs_op);
                    let new_rhs_range = rhs_range_fn(rhs_range.clone(), new_lhs, loc);
                    new_rhs.set_range_min(self, new_rhs_range.range_min());
                    new_rhs.set_range_max(self, new_rhs_range.range_max());
                } else if new_rhs.is_const(self) {
                    if matches!(op, RangeOp::Eq) {
                        let min =
                            Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));
                        let max =
                            Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));
                        new_lhs.set_range_min(self, min);
                        new_lhs.set_range_max(self, max);
                    } else if !matches!(op, RangeOp::Neq) {
                        new_lhs.set_range_min(self, new_lhs_range.range_min());
                        new_lhs.set_range_max(self, new_lhs_range.range_max());
                    }
                } else {
                    // we know nothing about either
                    // println!("didnt know either");
                    // new_rhs.set_range_min(self, new_rhs_range.range_min());
                    // new_rhs.set_range_max(self, new_rhs_range.range_max());
                    // any_unsat |= new_rhs_range.unsat(self);
                }
            } else {
                todo!("here: {:?}", new_rhs.underlying(self));
            }

            if let Some(backing_arr) = new_lhs.len_var_to_array(self) {
                if let Some(r) = backing_arr.range(self) {
                    let min = r.range_min();
                    let max = r.range_max();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(new_lhs.into(), loc));
                        backing_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(new_lhs.into(), loc));
                        backing_arr.set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }
            } else if let Some(arr) = new_lhs.index_to_array(self) {
                if let Some(index) = new_lhs.index_access_to_index(self) {
                    let next_arr = self.advance_var_in_ctx(arr, loc, ctx);
                    if next_arr.underlying(self).ty.is_dyn_builtin(self) {
                        if let Some(r) = next_arr.range(self) {
                            let min = r.evaled_range_min(self);
                            let max = r.evaled_range_max(self);

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.val.insert(
                                    Elem::Dynamic(Dynamic::new(index.into(), loc)),
                                    Elem::Dynamic(Dynamic::new(new_rhs.into(), loc)),
                                );
                                next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.val.insert(
                                    Elem::Dynamic(Dynamic::new(index.into(), loc)),
                                    Elem::Dynamic(Dynamic::new(new_rhs.into(), loc)),
                                );
                                next_arr.set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            }
                        }
                    }
                }
            }

            if let Some(backing_arr) = new_rhs.len_var_to_array(self) {
                if let Some(r) = backing_arr.range(self) {
                    let min = r.range_min();
                    let max = r.range_max();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(new_lhs.into(), loc));
                        backing_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(new_lhs.into(), loc));
                        backing_arr.set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }
            }

            let tmp_var = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self),
                    new_lhs.name(self),
                    op.to_string(),
                    new_rhs.name(self),
                ),
                display_name: format!(
                    "({} {} {})",
                    new_lhs.display_name(self),
                    op.to_string(),
                    new_rhs.display_name(self),
                ),
                storage: None,
                is_tmp: true,
                tmp_of: Some(TmpConstruction::new(new_lhs, op, Some(new_rhs))),
                is_symbolic: new_lhs.is_symbolic(self) || new_rhs.is_symbolic(self),
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                    SolcRange::from(Concrete::Bool(true)),
                ),
            };

            let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

            tmp_cvar = Some(cvar);

            any_unsat |= new_lhs_range.unsat(self);
            if any_unsat {
                ctx.kill(self, loc);
                return None;
            }

            ctx.add_ctx_dep(cvar, self);
        }

        if let Some(tmp) = new_lhs.tmp_of(self) {
            if tmp.op.inverse().is_some() {
                println!("range recursion: {:?}", tmp);
                self.range_recursion(tmp, recursion_ops, new_rhs, ctx, loc, &mut any_unsat)
            } else {
                self.uninvertable_range_recursion(tmp, new_lhs, new_rhs, loc, ctx);
                // println!("did not recurse as it was not reversable: {:?}", tmp);
            }
        }

        tmp_cvar
    }

    fn uninvertable_range_recursion(
        &mut self,
        tmp_construction: TmpConstruction,
        _new_lhs_core: ContextVarNode,
        _rhs_cvar: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) {
        if !tmp_construction.lhs.is_const(self) {
            // widen to maximum range :(
            let new_underlying_lhs =
                self.advance_var_in_ctx(tmp_construction.lhs.latest_version(self), loc, ctx);
            if let Some(lhs_range) = tmp_construction.lhs.range(self) {
                match lhs_range.evaled_range_min(self) {
                    Elem::Concrete(c) => {
                        new_underlying_lhs.set_range_min(
                            self,
                            Elem::Concrete(RangeConcrete {
                                val: Concrete::min(&c.val).unwrap_or_else(|| c.val.clone()),
                                loc,
                            }),
                        );
                        new_underlying_lhs.set_range_max(
                            self,
                            Elem::Concrete(RangeConcrete {
                                val: Concrete::max(&c.val).unwrap_or(c.val),
                                loc,
                            }),
                        );
                    }
                    _ => todo!(),
                }
            }
        }
    }

    /// Recursively updates the range for a
    fn range_recursion(
        &mut self,
        tmp_construction: TmpConstruction,
        (flip_op, no_flip_op): (RangeOp, RangeOp),
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        any_unsat: &mut bool,
    ) {
        // handle lhs
        let inverse = tmp_construction
            .op
            .inverse()
            .expect("impossible to not invert op");
        if !tmp_construction.lhs.is_const(self) {
            let adjusted_gt_rhs = ContextVarNode::from(
                self.op(
                    loc,
                    rhs_cvar,
                    tmp_construction.rhs.expect("No rhs in tmp_construction"),
                    ctx,
                    inverse,
                    false,
                )
                .expect_single()
                .1,
            );
            let new_underlying_lhs =
                self.advance_var_in_ctx(tmp_construction.lhs.latest_version(self), loc, ctx);
            if let Some(lhs_range) = new_underlying_lhs.underlying(self).ty.range(self) {
                if let Some(_rhs_range) = adjusted_gt_rhs.underlying(self).ty.range(self) {
                    let lhs_range_fn = SolcRange::dyn_fn_from_op(no_flip_op);
                    let new_lhs_range = lhs_range_fn(lhs_range, adjusted_gt_rhs, loc);

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
                            (flip_op, no_flip_op),
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
                    RangeOp::Sub => {
                        let concrete = ConcreteNode(
                            self.add_node(Node::Concrete(Concrete::Int(256, I256::from(-1i32))))
                                .index(),
                        );
                        let lhs_cvar = ContextVar::new_from_concrete(loc, concrete, self);
                        let tmp_lhs =
                            ContextVarNode::from(self.add_node(Node::ContextVar(lhs_cvar)));
                        let tmp_rhs = ContextVarNode::from(
                            self.op(loc, rhs_cvar, tmp_lhs, ctx, RangeOp::Mul, false)
                                .expect_single()
                                .1,
                        );
                        let new_rhs = ContextVarNode::from(
                            self.op(loc, tmp_rhs, tmp_construction.lhs, ctx, inverse, false)
                                .expect_single()
                                .1,
                        );
                        (true, new_rhs)
                    }
                    RangeOp::Add => {
                        let new_rhs = ContextVarNode::from(
                            self.op(loc, rhs_cvar, tmp_construction.lhs, ctx, inverse, false)
                                .expect_single()
                                .1,
                        );
                        (false, new_rhs)
                    }
                    e => panic!("here {e:?}"),
                };

                let new_underlying_rhs = self.advance_var_in_ctx(rhs, loc, ctx);
                if let Some(lhs_range) = new_underlying_rhs.underlying(self).ty.range(self) {
                    if let Some(_rhs_range) = adjusted_gt_rhs.underlying(self).ty.range(self) {
                        let new_lhs_range = if needs_inverse {
                            let lhs_range_fn = SolcRange::dyn_fn_from_op(flip_op);
                            lhs_range_fn(lhs_range, adjusted_gt_rhs, loc)
                        } else {
                            let lhs_range_fn = SolcRange::dyn_fn_from_op(no_flip_op);
                            lhs_range_fn(lhs_range, adjusted_gt_rhs, loc)
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
                                (flip_op, no_flip_op),
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
