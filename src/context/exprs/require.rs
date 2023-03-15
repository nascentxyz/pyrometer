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

use ethers_core::types::I256;
use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

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
                let lhs_paths = self.cmp(*loc, lhs, RangeOp::And, rhs, ctx);
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
    ) {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::CtxKilled) => {}
            (ExprRet::CtxKilled, _) => {}
            (ExprRet::SingleLiteral((lhs_ctx, lhs)), ExprRet::Single((_rhs_ctx, rhs))) => {
                ContextVarNode::from(*lhs).cast_from(&ContextVarNode::from(*rhs), self);
                self.handle_require_inner(
                    loc,
                    &ExprRet::Single((*lhs_ctx, *lhs)),
                    rhs_paths,
                    op,
                    rhs_op,
                    recursion_ops,
                )
            }
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

        // println!("lhs: {} - {:?}, rhs: {} - {:?}", new_lhs.display_name(self), new_lhs.is_const(self), new_rhs.display_name(self), new_rhs.is_const(self));

        if let Some(mut lhs_range) = new_lhs.underlying(self).ty.range(self) {
            let lhs_range_fn = SolcRange::dyn_fn_from_op(op);
            lhs_range.update_deps(ctx, self);
            let mut new_var_range = lhs_range_fn(lhs_range.clone(), new_rhs, loc);

            if let Some(mut rhs_range) = new_rhs.range(self) {
                rhs_range.update_deps(ctx, self);
                let lhs_is_const = new_lhs.is_const(self);
                let rhs_is_const = new_rhs.is_const(self);
                match (lhs_is_const, rhs_is_const) {
                    (true, true) => {
                        if self.const_killable(op, lhs_range, rhs_range) {
                            ctx.kill(self, loc);
                            return None;
                        }
                    }
                    (true, false) => {
                        // flip the new range around to be in terms of rhs
                        let rhs_range_fn = SolcRange::dyn_fn_from_op(rhs_op);
                        new_var_range = rhs_range_fn(rhs_range.clone(), new_lhs, loc);

                        if self.update_nonconst_from_const(loc, op, new_lhs, new_rhs, rhs_range) {
                            ctx.kill(self, loc);
                            return None;
                        }
                    }
                    (false, true) => {
                        if self.update_nonconst_from_const(loc, op, new_rhs, new_lhs, lhs_range) {
                            ctx.kill(self, loc);
                            return None;
                        }
                    }
                    (false, false) => {
                        if self.update_nonconst_from_nonconst(
                            loc, op, new_lhs, new_rhs, lhs_range, rhs_range,
                        ) {
                            ctx.kill(self, loc);
                            return None;
                        }
                    }
                }
            } else {
                todo!(
                    "Require: right hand side didnt have a range, likely invalid solidity - {:?}",
                    new_rhs.underlying(self)
                );
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

            any_unsat |= new_var_range.unsat(self);
            if any_unsat {
                ctx.kill(self, loc);
                return None;
            }

            ctx.add_ctx_dep(cvar, self);
        }

        if let Some(tmp) = new_lhs.tmp_of(self) {
            if tmp.op.inverse().is_some() {
                self.range_recursion(tmp, recursion_ops, new_rhs, ctx, loc, &mut any_unsat)
            } else {
                self.uninvertable_range_recursion(tmp, new_lhs, new_rhs, loc, ctx);
            }
        }

        tmp_cvar
    }

    /// Checks and returns whether the require statement is killable (i.e. impossible)
    fn const_killable(&mut self, op: RangeOp, lhs_range: SolcRange, rhs_range: SolcRange) -> bool {
        // check that the op is satisfied, return it as a bool
        match op {
            RangeOp::Eq => !lhs_range
                .evaled_range_min(self)
                .range_eq(&rhs_range.evaled_range_min(self)),
            RangeOp::Neq => lhs_range
                .evaled_range_min(self)
                .range_eq(&rhs_range.evaled_range_min(self)),
            RangeOp::Gt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .range_ord(&rhs_range.evaled_range_min(self)),
                    Some(Ordering::Equal) | Some(Ordering::Less)
                )
            }
            RangeOp::Gte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .range_ord(&rhs_range.evaled_range_min(self)),
                    Some(Ordering::Less)
                )
            }
            RangeOp::Lt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .range_ord(&rhs_range.evaled_range_min(self)),
                    Some(Ordering::Equal) | Some(Ordering::Greater)
                )
            }
            RangeOp::Lte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .range_ord(&rhs_range.evaled_range_min(self)),
                    Some(Ordering::Greater)
                )
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
    }

    /// Given a const var and a nonconst range, update the range based on the op
    fn update_nonconst_from_const(
        &mut self,
        loc: Loc,
        op: RangeOp,
        const_var: ContextVarNode,
        nonconst_var: ContextVarNode,
        mut nonconst_range: SolcRange,
    ) -> bool {
        match op {
            RangeOp::Eq => {
                // check that the constant is contained in the nonconst var range
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                if !nonconst_range.contains_elem(&elem, self) {
                    return true;
                }
                // if its contained, we can set the min & max to it
                nonconst_var.set_range_min(self, elem.clone());
                nonconst_var.set_range_max(self, elem);
                false
            }
            RangeOp::Neq => {
                // check if contains
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                // potentially add the const var as a range exclusion
                if let Some(Ordering::Equal) =
                    nonconst_range.evaled_range_min(self).range_ord(&elem)
                {
                    // mins are equivalent, add 1 instead of adding an exclusion
                    let min = nonconst_range
                        .evaled_range_min(self)
                        .maybe_concrete()
                        .expect("Was not concrete");
                    let one = Concrete::one(&min.val).expect("Cannot increment range elem by one");
                    let min = nonconst_range.range_min() + Elem::from(one);
                    nonconst_var.set_range_min(self, min);
                } else if let Some(std::cmp::Ordering::Equal) =
                    nonconst_range.evaled_range_max(self).range_ord(&elem)
                {
                    // maxs are equivalent, subtract 1 instead of adding an exclusion
                    let max = nonconst_range
                        .evaled_range_max(self)
                        .maybe_concrete()
                        .expect("Was not concrete");
                    let one = Concrete::one(&max.val).expect("Cannot decrement range elem by one");
                    let max = nonconst_range.range_max() - Elem::from(one);
                    nonconst_var.set_range_max(self, max);
                } else {
                    // just add as an exclusion
                    nonconst_range.exclusions.push(elem);
                    nonconst_var.set_range_exclusions(self, nonconst_range.exclusions);
                }

                false
            }
            RangeOp::Gt => {
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                // if nonconst max is <= const, we can't make this true
                let max = nonconst_range.evaled_range_max(self);
                if matches!(
                    max.range_ord(&elem.minimize(self)),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return true;
                }

                // we add one to the element because its strict >
                let max_conc = max.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");
                nonconst_var.set_range_min(self, elem + one.into());
                false
            }
            RangeOp::Gte => {
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                // if nonconst max is < const, we can't make this true
                if matches!(
                    nonconst_range
                        .evaled_range_max(self)
                        .range_ord(&elem.minimize(self)),
                    Some(Ordering::Less)
                ) {
                    return true;
                }

                nonconst_var.set_range_min(self, elem);
                false
            }
            RangeOp::Lt => {
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                // if nonconst min is >= const, we can't make this true
                let min = nonconst_range.evaled_range_min(self);
                if matches!(
                    min.range_ord(&elem.minimize(self)),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return true;
                }

                // we add one to the element because its strict >
                let min_conc = min.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                nonconst_var.set_range_max(self, elem - one.into());
                false
            }
            RangeOp::Lte => {
                let elem = Elem::Dynamic(Dynamic::new(const_var.latest_version(self).into(), loc));

                // if nonconst min is > const, we can't make this true
                let min = nonconst_range.evaled_range_min(self);
                if matches!(min.range_ord(&elem.minimize(self)), Some(Ordering::Greater)) {
                    return true;
                }

                nonconst_var.set_range_max(self, elem);
                false
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
    }

    /// Given a const var and a nonconst range, update the range based on the op. Returns whether its impossible
    fn update_nonconst_from_nonconst(
        &mut self,
        loc: Loc,
        op: RangeOp,
        new_lhs: ContextVarNode,
        new_rhs: ContextVarNode,
        mut lhs_range: SolcRange,
        mut rhs_range: SolcRange,
    ) -> bool {
        match op {
            RangeOp::Eq => {
                // check that there is overlap in the ranges
                if !lhs_range.overlaps(&rhs_range, self) {
                    return true;
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_min(self)
                    .range_ord(&rhs_range.evaled_range_min(self))
                {
                    Some(Ordering::Greater) => {
                        // take lhs range min as its tigher
                        new_rhs.set_range_min(self, lhs_range.range_min());
                    }
                    Some(Ordering::Less) => {
                        // take rhs range min as its tigher
                        new_lhs.set_range_min(self, rhs_range.range_min());
                    }
                    _ => {
                        // equal or not comparable - both keep their minimums
                    }
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_max(self)
                    .range_ord(&rhs_range.evaled_range_max(self))
                {
                    Some(Ordering::Less) => {
                        // take lhs range min as its tigher
                        new_rhs.set_range_max(self, lhs_range.range_max());
                    }
                    Some(Ordering::Greater) => {
                        // take rhs range min as its tigher
                        new_lhs.set_range_max(self, rhs_range.range_max());
                    }
                    _ => {
                        // equal or not comparable - both keep their maximums
                    }
                }

                false
            }
            RangeOp::Neq => {
                let rhs_elem =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));
                // just add as an exclusion
                lhs_range.exclusions.push(rhs_elem);
                new_lhs.set_range_exclusions(self, lhs_range.exclusions);

                let lhs_elem =
                    Elem::Dynamic(Dynamic::new(new_lhs.latest_version(self).into(), loc));
                // just add as an exclusion
                rhs_range.exclusions.push(lhs_elem);
                new_rhs.set_range_exclusions(self, rhs_range.exclusions);
                false
            }
            RangeOp::Gt => {
                let rhs_elem =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));

                // if lhs.max is <= rhs.min, we can't make this true
                let max = lhs_range.evaled_range_max(self);
                if matches!(
                    max.range_ord(&rhs_elem.minimize(self)),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return true;
                }

                let max_conc = max.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");

                // we add/sub one to the element because its strict >
                new_lhs.set_range_min(self, rhs_elem + one.clone().into());
                new_rhs.set_range_max(self, lhs_range.range_min() - one.into());
                false
            }
            RangeOp::Gte => {
                let rhs_elem =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));

                // if lhs.max is < rhs.min, we can't make this true
                if matches!(
                    lhs_range
                        .evaled_range_max(self)
                        .range_ord(&rhs_elem.minimize(self)),
                    Some(Ordering::Less)
                ) {
                    return true;
                }

                new_lhs.set_range_min(self, rhs_elem);
                new_rhs.set_range_max(self, lhs_range.range_min());
                false
            }
            RangeOp::Lt => {
                let rhs_elem =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));

                // if lhs min is >= rhs.max, we can't make this true
                let min = lhs_range.evaled_range_min(self);
                if matches!(
                    min.range_ord(&rhs_elem.minimize(self)),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return true;
                }

                // we add/sub one to the element because its strict >
                let min_conc = min.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                new_lhs.set_range_max(self, rhs_elem - one.clone().into());
                new_rhs.set_range_min(self, lhs_range.range_max() + one.into());
                false
            }
            RangeOp::Lte => {
                let rhs_elem =
                    Elem::Dynamic(Dynamic::new(new_rhs.latest_version(self).into(), loc));

                // if nonconst min is > const, we can't make this true
                let min = lhs_range.evaled_range_min(self);
                if matches!(
                    min.range_ord(&rhs_elem.minimize(self)),
                    Some(Ordering::Greater)
                ) {
                    return true;
                }

                new_lhs.set_range_max(self, rhs_elem);
                new_rhs.set_range_max(self, lhs_range.range_min());
                false
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
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
