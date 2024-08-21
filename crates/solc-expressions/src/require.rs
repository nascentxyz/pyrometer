use crate::{Assign, BinOp, ErrType, SolcError, Variable};

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode,
        ExprRet, KilledKind, TmpConstruction,
    },
    range_string::ToRangeString,
    AnalyzerBackend, ContextEdge, Edge, Node, Range, RangeEval, SolcRange, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::Loc;

use std::cmp::Ordering;

impl<T> Require for T where T: Variable + BinOp + Sized + AnalyzerBackend {}

/// Deals with require and assert statements, as well as adjusts bounds for variables
pub trait Require: AnalyzerBackend + Variable + BinOp + Sized {
    /// Do matching on [`ExprRet`]s to actually perform the require statement evaluation
    fn handle_require_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        op: RangeOp,
        err: Option<ErrType>,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (_, ExprRet::CtxKilled(..)) | (ExprRet::CtxKilled(..), _) => Ok(()),
            (ExprRet::SingleLiteral(lhs), ExprRet::SingleLiteral(rhs)) => self
                .handle_require_inner(
                    arena,
                    ctx,
                    &ExprRet::Single(*lhs),
                    &ExprRet::Single(*rhs),
                    op,
                    err,
                    loc,
                ),
            (ExprRet::SingleLiteral(lhs), ExprRet::Single(rhs)) => {
                // ie: require(5 == a);
                ContextVarNode::from(*lhs)
                    .cast_from(&ContextVarNode::from(*rhs), self, arena)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    arena,
                    ctx,
                    &ExprRet::Single(*lhs),
                    rhs_paths,
                    op,
                    err,
                    loc,
                )
            }
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                // ie: require(a == 5);
                ContextVarNode::from(*rhs)
                    .cast_from(&ContextVarNode::from(*lhs), self, arena)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    arena,
                    ctx,
                    lhs_paths,
                    &ExprRet::Single(*rhs),
                    op,
                    err,
                    loc,
                )
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                // ie: require(a == b);
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let new_lhs = self.advance_var_in_ctx(arena, lhs_cvar, loc, ctx)?;
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                let new_rhs = self.advance_var_in_ctx(arena, rhs_cvar, loc, ctx)?;

                self.require(
                    arena,
                    ctx,
                    new_lhs,
                    new_rhs,
                    op,
                    err.unwrap_or_default(),
                    loc,
                )?;
                Ok(())
            }
            (l @ ExprRet::Single(_) | l @ ExprRet::SingleLiteral(_), ExprRet::Multi(rhs_sides)) => {
                // ie: require(a == (b, c)); (not possible)
                rhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(arena, ctx, l, expr_ret, op, err, loc)
                })
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                // ie: require((a, b) == c); (not possible)
                lhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(arena, ctx, expr_ret, r, op, err, loc)
                })
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // ie: require((a, b) == (c, d)); (not possible)
                // ie: require((a, b) == (c, d, e)); (not possible)
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    // ie: require((a, b) == (c, d)); (not possible)
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.handle_require_inner(
                                arena,
                                ctx,
                                lhs_expr_ret,
                                rhs_expr_ret,
                                op,
                                err,
                                loc,
                            )
                        },
                    )
                } else {
                    // ie: require((a, b) == (c, d, e)); (not possible)
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.handle_require_inner(arena, ctx, lhs_paths, rhs_expr_ret, op, err, loc)
                    })
                }
            }
        }
    }

    /// Updates the range bounds for the variables passed into the require function. If the lefthand side is a temporary value,
    /// it will recursively update the range bounds for the underlying variable
    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "trace", skip_all)]
    fn require(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        mut new_lhs: ContextVarNode,
        mut new_rhs: ContextVarNode,
        op: RangeOp,
        err: ErrType,
        loc: Loc,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        let og_lhs = new_lhs;
        let og_rhs = new_rhs;
        tracing::trace!(
            "require: {} {op} {}",
            new_lhs.display_name(self).into_expr_err(loc)?,
            new_rhs.display_name(self).into_expr_err(loc)?
        );
        let mut any_unsat = false;
        let mut tmp_cvar = None;

        let rhs_op = op.require_rhs().unwrap();

        if let Some(lhs_range) = new_lhs
            .latest_version_or_inherited_in_ctx(ctx, self)
            .range(self)
            .into_expr_err(loc)?
        {
            let lhs_range_fn = SolcRange::dyn_fn_from_op(op);
            let mut new_var_range = lhs_range_fn(lhs_range.clone(), new_rhs);

            if let Some(rhs_range) = new_rhs.range(self).into_expr_err(loc)? {
                let lhs_is_const = new_lhs.is_const(self, arena).into_expr_err(loc)?;
                let rhs_is_const = new_rhs.is_const(self, arena).into_expr_err(loc)?;
                match (lhs_is_const, rhs_is_const) {
                    (true, true) => {
                        if self.const_killable(arena, op, lhs_range, rhs_range) {
                            tracing::trace!("const killable");
                            let err = self.add_err_node(ctx, err, loc)?;
                            ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (true, false) => {
                        // flip the new range around to be in terms of rhs
                        let rhs_range_fn = SolcRange::dyn_fn_from_op(rhs_op);
                        new_var_range = rhs_range_fn(rhs_range.clone(), new_lhs);
                        if self.update_nonconst_from_const(
                            arena, ctx, loc, rhs_op, new_lhs, new_rhs, rhs_range,
                        )? {
                            tracing::trace!("half-const killable");
                            let err = self.add_err_node(ctx, err, loc)?;
                            ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, true) => {
                        if self.update_nonconst_from_const(
                            arena, ctx, loc, op, new_rhs, new_lhs, lhs_range,
                        )? {
                            tracing::trace!("half-const killable");
                            let err = self.add_err_node(ctx, err, loc)?;
                            ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, false) => {
                        if self.update_nonconst_from_nonconst(
                            arena, ctx, loc, op, new_lhs, new_rhs, lhs_range, rhs_range,
                        )? {
                            tracing::trace!("nonconst killable");
                            let err = self.add_err_node(ctx, err, loc)?;
                            ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                }
            } else {
                return Err(ExprErr::BadRange(
                    loc,
                    format!(
                        "Require: right hand side didnt have a range, likely invalid solidity - {:?}",
                        new_rhs.underlying(self).into_expr_err(loc)?
                    )
                ));
            }
            tracing::trace!("done range updating");
            new_rhs = new_rhs.latest_version_or_inherited_in_ctx(ctx, self);
            new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);

            let rhs_display_name = new_rhs.display_name(self).into_expr_err(loc)?;
            let display_name = if rhs_display_name == "true" {
                (new_lhs.display_name(self).into_expr_err(loc)?).to_string()
            } else {
                format!(
                    "({} {op} {rhs_display_name})",
                    new_lhs.display_name(self).into_expr_err(loc)?,
                )
            };

            // we take the previous version because for the solver we actually dont want the updated range
            let base = Elem::Expr(RangeExpr::new(og_lhs.into(), op, og_rhs.into()));

            // construct a temporary variable that represent the conditional we just checked
            let conditional_var = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self).into_expr_err(loc)?,
                    new_lhs.name(self).into_expr_err(loc)?,
                    op,
                    new_rhs.name(self).into_expr_err(loc)?,
                ),
                display_name: display_name.clone(),
                storage: None,
                is_tmp: true,
                tmp_of: Some(TmpConstruction::new(new_lhs, op, Some(new_rhs))),
                dep_on: {
                    let mut deps = new_lhs.dependent_on(self, true).into_expr_err(loc)?;
                    deps.extend(new_rhs.dependent_on(self, true).into_expr_err(loc)?);
                    deps.sort();
                    deps.dedup();
                    Some(deps)
                },
                is_symbolic: new_lhs.is_symbolic(self).into_expr_err(loc)?
                    || new_rhs.is_symbolic(self).into_expr_err(loc)?,
                is_return: false,
                is_fundamental: None,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                    // we set the minimum to `true` so that if `elem` evaluates to false,
                    // we can discover the unsatisifiability
                    Some(SolcRange::new(base.clone(), base, vec![])),
                ),
            };

            let conditional_cvar = ContextVarNode::from(self.add_node(conditional_var));
            ctx.add_var(conditional_cvar, self).into_expr_err(loc)?;
            self.add_edge(conditional_cvar, ctx, Edge::Context(ContextEdge::Variable));

            let cnode = ConcreteNode::from(self.add_node(Concrete::Bool(true)));
            let tmp_true = Node::ContextVar(
                ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                    .into_expr_err(loc)?,
            );

            // construct a temporary `true` node
            let tmp_true = ContextVarNode::from(self.add_node(tmp_true));

            // construct a temporary var that will be used as the ctx dependency
            let tmp_var = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}(({} {} {}) == true)",
                    ctx.new_tmp(self).into_expr_err(loc)?,
                    new_lhs.name(self).into_expr_err(loc)?,
                    op,
                    new_rhs.name(self).into_expr_err(loc)?,
                ),
                display_name: format!("{display_name} == true"),
                storage: None,
                is_tmp: true,
                tmp_of: Some(TmpConstruction::new(
                    tmp_true,
                    RangeOp::Eq,
                    Some(conditional_cvar),
                )),
                dep_on: {
                    let mut deps = tmp_true.dependent_on(self, true).into_expr_err(loc)?;
                    deps.extend(
                        conditional_cvar
                            .dependent_on(self, true)
                            .into_expr_err(loc)?,
                    );
                    Some(deps)
                },
                is_symbolic: new_lhs.is_symbolic(self).into_expr_err(loc)?
                    || new_rhs.is_symbolic(self).into_expr_err(loc)?,
                is_return: false,
                is_fundamental: None,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                    // we set the minimum to `true` so that if `elem` evaluates to false,
                    // we can discover the unsatisifiability
                    Some(SolcRange::new(
                        Elem::from(Concrete::from(true)),
                        Elem::from(conditional_cvar),
                        vec![],
                    )),
                ),
            };

            let cvar = ContextVarNode::from(self.add_node(tmp_var));
            ctx.add_var(cvar, self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

            tmp_cvar = Some(cvar);

            tracing::trace!("checking unsat");
            any_unsat |= new_var_range.unsat(self, arena);

            ctx.add_ctx_dep(conditional_cvar, self, arena)
                .into_expr_err(loc)?;

            if any_unsat || ctx.unreachable(self, arena).into_expr_err(loc)? {
                let err = self.add_err_node(ctx, err, loc)?;
                ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                return Ok(None);
            }
        }

        tracing::trace!(
            "{} is tmp: {}",
            new_lhs.display_name(self).unwrap(),
            new_lhs.is_tmp(self).unwrap()
        );

        self.maybe_assign_to_parent_array(
            arena,
            ctx,
            og_rhs,
            new_rhs.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
        )?;
        self.maybe_assign_to_parent_array(
            arena,
            ctx,
            og_lhs,
            new_lhs.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
        )?;

        Ok(tmp_cvar)
    }

    /// Checks and returns whether the require statement is killable (i.e. impossible)
    fn const_killable(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        op: RangeOp,
        lhs_range: SolcRange,
        rhs_range: SolcRange,
    ) -> bool {
        // check that the op is satisfied, return it as a bool
        match op {
            RangeOp::Eq => !lhs_range
                .evaled_range_min(self, arena)
                .unwrap()
                .range_eq(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
            RangeOp::Neq => lhs_range
                .evaled_range_min(self, arena)
                .unwrap()
                .range_eq(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
            RangeOp::Gt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self, arena)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
                    Some(Ordering::Equal) | Some(Ordering::Less)
                )
            }
            RangeOp::Gte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self, arena)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
                    Some(Ordering::Less)
                )
            }
            RangeOp::Lt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self, arena)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
                    Some(Ordering::Equal) | Some(Ordering::Greater)
                )
            }
            RangeOp::Lte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self, arena)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self, arena).unwrap(), arena),
                    Some(Ordering::Greater)
                )
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
    }

    /// Given a const var and a nonconst range, update the range based on the op
    #[tracing::instrument(level = "trace", skip_all)]
    fn update_nonconst_from_const(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        op: RangeOp,
        const_var: ContextVarNode,
        nonconst_var: ContextVarNode,
        mut nonconst_range: SolcRange,
    ) -> Result<bool, ExprErr> {
        tracing::trace!("Setting range for nonconst from const");

        let prev_nonconst = nonconst_var.previous_version(self);
        let u_mut = nonconst_var.underlying_mut(self).into_expr_err(loc)?;
        if let Some(ref mut dep_on) = u_mut.dep_on {
            dep_on.push(const_var);
            if let Some(prev) = prev_nonconst {
                dep_on.push(prev);
            };
            dep_on.sort();
            dep_on.dedup();
        } else {
            let deps = if let Some(prev) = prev_nonconst {
                vec![const_var, prev]
            } else {
                vec![const_var]
            };
            u_mut.dep_on = Some(deps);
        }

        match op {
            RangeOp::Eq => {
                // check that the constant is contained in the nonconst var range
                let elem = Elem::from(nonconst_var).assign(Elem::from(
                    const_var.latest_version_or_inherited_in_ctx(ctx, self),
                ));
                let evaled_min = nonconst_range
                    .evaled_range_min(self, arena)
                    .into_expr_err(loc)?;
                if evaled_min.maybe_concrete().is_none() {
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug (update nonconst from const: Eq). {}.min: {}", nonconst_var.display_name(self).unwrap(), evaled_min.to_range_string(false, self, arena).s)));
                }

                if !nonconst_range.contains_elem(&elem, self, arena) {
                    return Ok(true);
                }
                // if its contained, we can set the min & max to it
                nonconst_var
                    .set_range_min(self, arena, elem.clone())
                    .into_expr_err(loc)?;
                nonconst_var
                    .set_range_max(self, arena, elem)
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Neq => {
                // check if contains
                let mut elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self))
                    .minimize(self, arena)
                    .unwrap();

                // potentially add the const var as a range exclusion
                if let Some(Ordering::Equal) = nonconst_range
                    .evaled_range_min(self, arena)
                    .into_expr_err(loc)?
                    .range_ord(&elem, arena)
                {
                    // mins are equivalent, add 1 instead of adding an exclusion
                    let min = nonconst_range
                        .evaled_range_min(self, arena)
                        .into_expr_err(loc)?;
                    let Some(min) = min.maybe_concrete() else {
                        return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug (update nonconst from const: Neq). Min: {}", min.to_range_string(false, self, arena).s)));
                    };
                    let one = Concrete::one(&min.val).expect("Cannot increment range elem by one");
                    let min = nonconst_range.range_min().into_owned() + Elem::from(one);
                    nonconst_var
                        .set_range_min(self, arena, min)
                        .into_expr_err(loc)?;
                } else if let Some(std::cmp::Ordering::Equal) = nonconst_range
                    .evaled_range_max(self, arena)
                    .into_expr_err(loc)?
                    .range_ord(&elem, arena)
                {
                    // maxs are equivalent, subtract 1 instead of adding an exclusion
                    let max = nonconst_range
                        .evaled_range_max(self, arena)
                        .into_expr_err(loc)?;

                    let Some(max) = max.maybe_concrete() else {
                        return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug (update nonconst from const: Neq 2). Max: {}", max.to_range_string(true, self, arena).s)));
                    };
                    let one = Concrete::one(&max.val).expect("Cannot decrement range elem by one");
                    let max = nonconst_range.range_max().into_owned() - Elem::from(one);
                    nonconst_var
                        .set_range_max(self, arena, max)
                        .into_expr_err(loc)?;
                } else {
                    // just add as an exclusion
                    elem.arenaize(self, arena).into_expr_err(loc)?;
                    nonconst_range.add_range_exclusion(elem);
                    nonconst_var
                        .set_range_exclusions(self, nonconst_range.exclusions)
                        .into_expr_err(loc)?;
                }

                Ok(false)
            }
            RangeOp::Gt => {
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));

                // if nonconst max is <= const, we can't make this true
                let max = nonconst_range
                    .evaled_range_max(self, arena)
                    .into_expr_err(loc)?;
                if matches!(
                    max.range_ord(&elem.minimize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add one to the element because its strict >
                let Some(max_conc) = const_var
                    .evaled_range_min(self, arena)
                    .unwrap()
                    .unwrap()
                    .maybe_concrete()
                else {
                    return Err(ExprErr::BadRange(loc, format!(
                        "Expected {} to have a concrete range by now. This is likely a bug (update nonconst from const: Gt). Max: {}, expr: {} {} {}, const value: {}",
                        nonconst_var.display_name(self).unwrap(),
                        nonconst_range.max,
                        nonconst_var.display_name(self).unwrap(),
                        op,
                        const_var.display_name(self).unwrap(),
                        const_var.evaled_range_min(self, arena).unwrap().unwrap()
                    )));
                };
                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");
                nonconst_var
                    .set_range_min(
                        self,
                        arena,
                        (elem + one.into()).max(nonconst_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Gte => {
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));

                // if nonconst max is < const, we can't make this true
                if matches!(
                    nonconst_range
                        .evaled_range_max(self, arena)
                        .into_expr_err(loc)?
                        .range_ord(&elem.minimize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Less)
                ) {
                    return Ok(true);
                }

                nonconst_var
                    .set_range_min(
                        self,
                        arena,
                        elem.max(nonconst_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lt => {
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));

                // if nonconst min is >= const, we can't make this true
                let min = nonconst_range
                    .evaled_range_min(self, arena)
                    .into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&elem.minimize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add one to the element because its strict >

                let Some(min_conc) = min.maybe_concrete() else {
                    return Err(ExprErr::BadRange(loc, format!("Expected {} to have a concrete range by now. This is likely a bug (update nonconst from const: Lt). Min: {}", nonconst_var.display_name(self).unwrap(), nonconst_range.min)));
                };
                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                nonconst_var
                    .set_range_max(
                        self,
                        arena,
                        (elem - one.into()).min(nonconst_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lte => {
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));

                // if nonconst min is > const, we can't make this true
                let min = nonconst_range
                    .evaled_range_min(self, arena)
                    .into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&elem.minimize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Greater)
                ) {
                    return Ok(true);
                }

                nonconst_var
                    .set_range_max(
                        self,
                        arena,
                        elem.min(nonconst_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
    }

    /// Given a const var and a nonconst range, update the range based on the op. Returns whether its impossible
    fn update_nonconst_from_nonconst(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        op: RangeOp,
        new_lhs: ContextVarNode,
        new_rhs: ContextVarNode,
        mut lhs_range: SolcRange,
        mut rhs_range: SolcRange,
    ) -> Result<bool, ExprErr> {
        tracing::trace!("Setting range for nonconst from nonconst");

        let prev_nonconst = new_lhs.previous_version(self);
        let u_mut = new_lhs.underlying_mut(self).into_expr_err(loc)?;
        if let Some(ref mut dep_on) = u_mut.dep_on {
            dep_on.push(new_rhs);
            if let Some(prev) = prev_nonconst {
                dep_on.push(prev);
            };
            dep_on.sort();
            dep_on.dedup();
        } else {
            let deps = if let Some(prev) = prev_nonconst {
                vec![new_rhs, prev]
            } else {
                vec![new_rhs]
            };
            u_mut.dep_on = Some(deps);
        }

        let next_rhs = self.advance_var_in_ctx_forcible(arena, new_rhs, loc, ctx, true)?;
        let u_mut = next_rhs.underlying_mut(self).into_expr_err(loc)?;
        if let Some(ref mut dep_on) = u_mut.dep_on {
            dep_on.push(new_lhs);
            dep_on.push(new_rhs);
            dep_on.sort();
            dep_on.dedup();
        } else {
            u_mut.dep_on = Some(vec![new_lhs, new_rhs]);
        }
        let new_rhs = next_rhs;

        match op {
            RangeOp::Eq => {
                // check that there is overlap in the ranges
                if !lhs_range.overlaps(&rhs_range, self, arena) {
                    return Ok(true);
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_min(self, arena)
                    .into_expr_err(loc)?
                    .range_ord(
                        &rhs_range.evaled_range_min(self, arena).into_expr_err(loc)?,
                        arena,
                    ) {
                    Some(Ordering::Greater) => {
                        // take lhs range min as its tigher
                        new_rhs
                            .set_range_min(self, arena, Elem::from(new_rhs))
                            .into_expr_err(loc)?;
                    }
                    Some(Ordering::Less) => {
                        // take rhs range min as its tigher
                        new_lhs
                            .set_range_min(self, arena, rhs_range.range_min().into_owned())
                            .into_expr_err(loc)?;
                    }
                    _ => {
                        // equal or not comparable - both keep their minimums
                    }
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_max(self, arena)
                    .into_expr_err(loc)?
                    .range_ord(
                        &rhs_range.evaled_range_max(self, arena).into_expr_err(loc)?,
                        arena,
                    ) {
                    Some(Ordering::Less) => {
                        // take lhs range min as its tigher
                        new_rhs
                            .set_range_max(self, arena, lhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;
                    }
                    Some(Ordering::Greater) => {
                        // take rhs range min as its tigher
                        new_lhs
                            .set_range_max(self, arena, rhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;
                    }
                    _ => {
                        // equal or not comparable - both keep their maximums
                    }
                }

                Ok(false)
            }
            RangeOp::Neq => {
                if new_rhs == new_lhs {
                    return Ok(true);
                }

                let mut rhs_elem =
                    Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                // just add as an exclusion
                rhs_elem.arenaize(self, arena).into_expr_err(loc)?;
                lhs_range.add_range_exclusion(rhs_elem);
                new_lhs
                    .set_range_exclusions(self, lhs_range.exclusions)
                    .into_expr_err(loc)?;

                let mut lhs_elem =
                    Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self));
                // just add as an exclusion
                lhs_elem.arenaize(self, arena).into_expr_err(loc)?;
                rhs_range.add_range_exclusion(lhs_elem);
                new_rhs
                    .set_range_exclusions(self, rhs_range.exclusions)
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Gt => {
                let rhs_elem = Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                let lhs_elem = Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self));

                // if lhs.max is <= rhs.min, we can't make this true
                let max = lhs_range.evaled_range_max(self, arena).into_expr_err(loc)?;
                if matches!(
                    max.range_ord(&rhs_elem.minimize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                let Some(max_conc) = max.maybe_concrete() else {
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug (update nonconst from nonconst: Gt). Max: {}", max.to_range_string(true, self, arena).s)));
                };

                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");

                // we add/sub one to the element because its strict >
                new_lhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_min(
                        self,
                        arena,
                        (rhs_elem + one.clone().into()).max(lhs_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                new_rhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_max(
                        self,
                        arena,
                        (lhs_elem - one.into()).min(rhs_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;

                Ok(false)
            }
            RangeOp::Gte => {
                // lhs >= rhs
                // lhs min is the max of current lhs_min and rhs_min

                let rhs_elem = Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                let lhs_elem = Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self));

                // if lhs.max is < rhs.min, we can't make this true
                let max = lhs_range.evaled_range_max(self, arena).into_expr_err(loc)?;
                let min = rhs_elem.minimize(self, arena).into_expr_err(loc)?;
                if let Some(Ordering::Less) = max.range_ord(&min, arena) {
                    return Ok(true);
                }

                let new_min = Elem::Expr(RangeExpr::new(
                    new_lhs.latest_version_or_inherited_in_ctx(ctx, self).into(),
                    RangeOp::Max,
                    rhs_elem,
                ));
                let new_max = Elem::Expr(RangeExpr::new(
                    new_rhs.latest_version_or_inherited_in_ctx(ctx, self).into(),
                    RangeOp::Min,
                    lhs_elem,
                ));

                let new_new_lhs = self.advance_var_in_ctx(arena, new_lhs, loc, ctx)?;
                let new_new_rhs = self.advance_var_in_ctx(arena, new_rhs, loc, ctx)?;

                new_new_lhs
                    .set_range_min(self, arena, new_min.clone())
                    .into_expr_err(loc)?;
                new_new_rhs
                    .set_range_min(self, arena, new_max.clone())
                    .into_expr_err(loc)?;
                new_new_rhs
                    .set_range_max(self, arena, new_max)
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lt => {
                let rhs_elem = Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                let lhs_elem = Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self));

                // if lhs min is >= rhs.max, we can't make this true
                let min = lhs_range.evaled_range_min(self, arena).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&rhs_elem.maximize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add/sub one to the element because its strict >
                let Some(min_conc) = min.maybe_concrete() else {
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug (update nonconst from const: Lt). Min: {}", min.to_range_string(false, self, arena).s)));
                };

                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                let new_new_lhs = self.advance_var_in_ctx(arena, new_lhs, loc, ctx)?;
                let new_new_rhs = self.advance_var_in_ctx(arena, new_rhs, loc, ctx)?;

                new_new_lhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_max(
                        self,
                        arena,
                        (rhs_elem - one.clone().into()).min(lhs_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                new_new_rhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_min(
                        self,
                        arena,
                        (lhs_elem + one.into()).max(rhs_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lte => {
                let rhs_elem = Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                let lhs_elem = Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self))
                    .max(rhs_range.range_min().into_owned());

                // if nonconst min is > const, we can't make this true
                let min = lhs_range.evaled_range_min(self, arena).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&rhs_elem.maximize(self, arena).into_expr_err(loc)?, arena),
                    Some(Ordering::Greater)
                ) {
                    return Ok(true);
                }

                new_lhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_max(
                        self,
                        arena,
                        rhs_elem.min(lhs_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                new_rhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_min(self, arena, lhs_elem.clone())
                    .into_expr_err(loc)?;
                new_rhs
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .set_range_max(self, arena, lhs_elem)
                    .into_expr_err(loc)?;
                Ok(false)
            }
            e => todo!("Non-comparator in require, {e:?}"),
        }
    }
}
