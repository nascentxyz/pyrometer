use crate::{require::Require, variable::Variable, Assign, ErrType, SolcError};
use shared::GraphError;

use graph::{
    elem::*,
    nodes::{
        Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, KilledKind, TmpConstruction,
    },
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use alloy_primitives::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> BinOp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles binary operations (`+`, `-`, `/`, etc.)
pub trait BinOp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn cast_sides(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs: &ExprRet,
        rhs: &ExprRet,
        loc: Loc,
    ) -> Result<(ContextVarNode, ContextVarNode), GraphError> {
        // follow these rules https://docs.soliditylang.org/en/latest/types.html#operators
        let lhs_cvar =
            ContextVarNode::from(lhs.expect_single()?).latest_version_in_ctx(ctx, self)?;
        let rhs_cvar =
            ContextVarNode::from(rhs.expect_single()?).latest_version_in_ctx(ctx, self)?;
        if rhs.implicitly_castable_to_expr(self, lhs)? {
            let tmp = rhs_cvar.as_tmp(self, ctx, loc)?;
            tmp.cast_from(&lhs_cvar, self, arena)?;
            return Ok((lhs_cvar, tmp));
        }

        if lhs.implicitly_castable_to_expr(self, rhs)? {
            let tmp = lhs_cvar.as_tmp(self, ctx, loc)?;
            tmp.cast_from(&rhs_cvar, self, arena)?;
            return Ok((tmp, rhs_cvar));
        }
        Ok((lhs_cvar, rhs_cvar))
    }

    /// Evaluate and execute a binary operation expression
    fn op_match(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        op: RangeOp,
        assign: bool,
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::Null, _) => Err(ExprErr::NoLhs(
                loc,
                "No left hand side provided for binary operation".to_string(),
            )),
            (_, ExprRet::Null) => Err(ExprErr::NoRhs(
                loc,
                "No right hand side provided for binary operation".to_string(),
            )),
            (ExprRet::SingleLiteral(lhs), ExprRet::SingleLiteral(rhs)) => {
                // ie: 5 + 5
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                lhs_cvar.try_increase_size(self, arena).into_expr_err(loc)?;
                rhs_cvar.try_increase_size(self, arena).into_expr_err(loc)?;
                ctx.push_expr(
                    self.op(arena, loc, lhs_cvar, rhs_cvar, ctx, op, assign)?,
                    self,
                )
                .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::SingleLiteral(lhs), r @ ExprRet::Single(_)) => {
                // ie: 5 + x
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                lhs_cvar.try_increase_size(self, arena).into_expr_err(loc)?;
                let (lhs_cvar, rhs_cvar) = self
                    .cast_sides(
                        arena,
                        ctx,
                        &ExprRet::SingleLiteral(lhs_cvar.0.into()),
                        r,
                        loc,
                    )
                    .into_expr_err(loc)?;
                ctx.push_expr(
                    self.op(arena, loc, lhs_cvar, rhs_cvar, ctx, op, assign)?,
                    self,
                )
                .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), r @ ExprRet::SingleLiteral(_)) => {
                // ie: x + 5
                let (lhs_cvar, rhs_cvar) =
                    self.cast_sides(arena, ctx, l, r, loc).into_expr_err(loc)?;
                ctx.push_expr(
                    self.op(arena, loc, lhs_cvar, rhs_cvar, ctx, op, assign)?,
                    self,
                )
                .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), r @ ExprRet::Single(_)) => {
                // ie: x + y
                let (lhs_cvar, rhs_cvar) =
                    self.cast_sides(arena, ctx, l, r, loc).into_expr_err(loc)?;
                ctx.push_expr(
                    self.op(arena, loc, lhs_cvar, rhs_cvar, ctx, op, assign)?,
                    self,
                )
                .into_expr_err(loc)?;
                Ok(())
            }
            (lhs, ExprRet::Multi(rhs_sides)) => {
                // sometimes a single is wrapped in a multi as the result of a function return
                if rhs_sides.len() == 1 {
                    self.op_match(arena, ctx, loc, lhs, &rhs_sides[0], op, assign)
                } else {
                    Err(ExprErr::UnhandledCombo(
                        loc,
                        format!("Unhandled combination in binop: {lhs:?} {rhs_sides:?}"),
                    ))
                }
            }
            (ExprRet::Multi(lhs_sides), rhs) => {
                if lhs_sides.len() == 1 {
                    self.op_match(arena, ctx, loc, &lhs_sides[0], rhs, op, assign)
                } else {
                    Err(ExprErr::UnhandledCombo(
                        loc,
                        format!("Unhandled combination in binop: {lhs_sides:?} {rhs:?}"),
                    ))
                }
            }
            (_, ExprRet::CtxKilled(kind)) => ctx.kill(self, loc, *kind).into_expr_err(loc),
            (ExprRet::CtxKilled(kind), _) => ctx.kill(self, loc, *kind).into_expr_err(loc),
        }
    }

    /// Execute a binary operation after parsing the expressions
    #[tracing::instrument(level = "trace", skip_all)]
    fn op(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> Result<ExprRet, ExprErr> {
        // Given a lhs and rhs node
        //  - if assignment:
        //       - increment the version of the lhs
        //       - assign the new lhs to lhs + rhs
        //       - denote that the new lhs is dependent on the rhs
        //  - if not assignment:
        //      - create a temporary variable and add it to the context
        //      - assign the temporary variable to lhs + rhs
        //  - if checked math
        //      - put requirements on the new variable
        //  - apply any knock on effects to parents (if lhs or rhs is part of an array, update the parent)
        //  - add the result to the ctx return stack
        tracing::trace!(
            "binary op: {} {op} {}, assign: {}",
            lhs_cvar.display_name(self).into_expr_err(loc)?,
            rhs_cvar.display_name(self).into_expr_err(loc)?,
            assign
        );

        let unchecked = op.unchecked();
        let new_lhs = if assign {
            let new = self.advance_var_in_ctx_forcible(arena, lhs_cvar, loc, ctx, true)?;
            let underlying = new.underlying_mut(self).into_expr_err(loc)?;
            underlying.tmp_of = Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar)));

            if let Some(ref mut dep_on) = underlying.dep_on {
                dep_on.push(rhs_cvar);
            } else {
                new.set_dependent_on(self).into_expr_err(loc)?;
            }

            new
        } else {
            let mut new_lhs_underlying =
                ContextVar::new_bin_op_tmp(lhs_cvar, op, rhs_cvar, ctx, loc, self)
                    .into_expr_err(loc)?;

            // will potentially mutate the ty from concrete to builtin with a concrete range
            new_lhs_underlying
                .ty
                .concrete_to_builtin(self)
                .into_expr_err(loc)?;

            let new_var = self.add_node(new_lhs_underlying);
            ctx.add_var(new_var.into(), self).into_expr_err(loc)?;
            self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
            ContextVarNode::from(new_var)
        };

        let new_rhs = rhs_cvar.latest_version_or_inherited_in_ctx(ctx, self);

        let expr = Elem::Expr(RangeExpr::new(
            Elem::from(Reference::new(
                lhs_cvar
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .into(),
            )),
            op,
            Elem::from(new_rhs),
        ));

        let mut e = expr.clone();
        e.arenaize(self, arena).unwrap();

        let new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);
        new_lhs
            .set_range_min(self, arena, expr.clone())
            .into_expr_err(loc)?;
        new_lhs
            .set_range_max(self, arena, expr)
            .into_expr_err(loc)?;
        // to prevent some recursive referencing, forcibly increase lhs_cvar
        self.advance_var_in_ctx_forcible(
            arena,
            lhs_cvar.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
            ctx,
            true,
        )?;

        self.maybe_assign_to_parent_array(
            arena,
            ctx,
            rhs_cvar,
            new_rhs.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
        )?;
        self.maybe_assign_to_parent_array(
            arena,
            ctx,
            lhs_cvar,
            new_lhs.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
        )?;

        if !unchecked {
            match op {
                RangeOp::Div(..) | RangeOp::Mod => {
                    if let Some(killed) =
                        self.checked_require_mod_div(arena, lhs_cvar, new_rhs, loc, ctx)?
                    {
                        return Ok(killed);
                    }
                }
                RangeOp::Sub(..) => {
                    if let Some(killed) =
                        self.checked_require_sub(arena, lhs_cvar, new_lhs, new_rhs, loc, ctx)?
                    {
                        return Ok(killed);
                    }
                }
                RangeOp::Add(..) => {
                    if let Some(killed) =
                        self.checked_require_add(arena, lhs_cvar, new_lhs, new_rhs, loc, ctx)?
                    {
                        return Ok(killed);
                    }
                }
                RangeOp::Mul(..) => {
                    if let Some(killed) =
                        self.checked_require_mul(arena, lhs_cvar, new_lhs, new_rhs, loc, ctx)?
                    {
                        return Ok(killed);
                    }
                }
                RangeOp::Exp(..) => {
                    if let Some(killed) =
                        self.checked_require_exp(arena, lhs_cvar, new_lhs, new_rhs, loc, ctx)?
                    {
                        return Ok(killed);
                    }
                }
                _ => {}
            }
        }

        Ok(ExprRet::Single(
            new_lhs.latest_version_or_inherited_in_ctx(ctx, self).into(),
        ))
    }

    /// Perform bitwise not
    #[tracing::instrument(level = "trace", skip_all)]
    fn bit_not_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_expr: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match lhs_expr {
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)?;
                ctx.push_expr(lhs_expr, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::SingleLiteral(lhs) => {
                // TODO: try to pop from the stack and if there is a single element there
                // use it as a type hint, then place it back on the stack
                ContextVarNode::from(lhs)
                    .try_increase_size(self, arena)
                    .into_expr_err(loc)?;
                self.bit_not_inner(arena, ctx, ExprRet::Single(lhs), loc)?;
                Ok(())
            }
            ExprRet::Single(lhs) => {
                let lhs_cvar = ContextVarNode::from(lhs);
                tracing::trace!(
                    "bitwise not: {}",
                    lhs_cvar.display_name(self).into_expr_err(loc)?
                );
                let out_var = ContextVar {
                    loc: Some(loc),
                    name: format!(
                        "tmp{}(~{})",
                        ctx.new_tmp(self).into_expr_err(loc)?,
                        lhs_cvar.name(self).into_expr_err(loc)?,
                    ),
                    display_name: format!("~{}", lhs_cvar.display_name(self).into_expr_err(loc)?,),
                    storage: None,
                    is_tmp: true,
                    tmp_of: Some(TmpConstruction::new(lhs_cvar, RangeOp::BitNot, None)),
                    dep_on: Some(lhs_cvar.dependent_on(self, true).into_expr_err(loc)?),
                    is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                    is_return: false,
                    is_fundamental: None,
                    ty: lhs_cvar.underlying(self).into_expr_err(loc)?.ty.clone(),
                };

                let expr = Elem::Expr(RangeExpr::<Concrete>::new(
                    Elem::from(Reference::new(
                        lhs_cvar
                            .latest_version_or_inherited_in_ctx(ctx, self)
                            .into(),
                    )),
                    RangeOp::BitNot,
                    Elem::Null,
                ));

                let out_var = ContextVarNode::from(self.add_node(out_var));

                out_var
                    .set_range_min(self, arena, expr.clone())
                    .into_expr_err(loc)?;
                out_var
                    .set_range_max(self, arena, expr)
                    .into_expr_err(loc)?;

                self.advance_var_in_ctx_forcible(arena, lhs_cvar, loc, ctx, true)?;
                ctx.push_expr(ExprRet::Single(out_var.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Multi(f) => Err(ExprErr::MultiNot(
                loc,
                format!("Multiple elements in bitwise not expression: {f:?}"),
            )),
            ExprRet::Null => Err(ExprErr::NoRhs(
                loc,
                "No right hand side in `not` expression".to_string(),
            )),
        }
    }

    fn checked_require_mod_div(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        _lhs: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        // x / y || x % y
        // revert if div or mod by 0
        if rhs.is_const(self, arena).into_expr_err(loc)?
            && rhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .range_eq(&Elem::from(Concrete::from(U256::ZERO)), arena)
        {
            let err = self.add_err_node(ctx, ErrType::division(), loc)?;
            ctx.add_return_node(loc, err, self).into_expr_err(loc)?;
            let res = ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc);
            let _ = self.add_if_err(res);

            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // otherwise, require rhs != 0
        let tmp_rhs = self.advance_var_in_ctx(arena, rhs, loc, ctx)?;
        let zero_node = self.add_concrete_var(ctx, Concrete::from(U256::ZERO), loc)?;

        if self
            .require(
                arena,
                ctx,
                tmp_rhs,
                zero_node,
                RangeOp::Neq,
                ErrType::division(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }
        Ok(None)
    }

    fn checked_require_sub(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        lhs: ContextVarNode,
        new_lhs: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        // x - y >= type(x).min
        let new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);
        let tmp_lhs = self.advance_var_in_ctx_forcible(arena, new_lhs, loc, ctx, true)?;

        // in checked subtraction, we have to make sure x - y >= type(x).min ==> x >= type(x).min + y
        // get the lhs min
        let min_conc = lhs.ty_min_concrete(self).into_expr_err(loc)?.unwrap();
        let min: ContextVarNode = self.add_concrete_var(ctx, min_conc, loc)?;

        // require lhs - rhs >= type(lhs).min
        if self
            .require(
                arena,
                ctx,
                tmp_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                min,
                RangeOp::Gte,
                ErrType::arithmetic(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // If x and y are signed ints, we have to check that x - -y <= type(x).max
        // because it could overflow in the positive direction
        let lhs_is_int = lhs.is_int(self).into_expr_err(loc)?;
        let rhs_is_int = rhs.is_int(self).into_expr_err(loc)?;
        if lhs_is_int && rhs_is_int {
            let rhs_min = rhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?");
            if rhs_min.is_negative(false, self, arena).into_expr_err(loc)? {
                // rhs can be negative, require that lhs <= type(x).max + -rhs
                // get the lhs max
                let max_conc = lhs.ty_max_concrete(self).into_expr_err(loc)?.unwrap();
                let max: ContextVarNode = self.add_concrete_var(ctx, max_conc, loc)?;

                if self
                    .require(
                        arena,
                        ctx,
                        tmp_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                        max,
                        RangeOp::Lte,
                        ErrType::arithmetic(),
                        loc,
                    )?
                    .is_none()
                {
                    return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
                }
            }
        }
        Ok(None)
    }

    fn checked_require_add(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        lhs: ContextVarNode,
        new_lhs: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        // lhs + rhs <= type(lhs).max
        let new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);
        let tmp_lhs = self.advance_var_in_ctx_forcible(arena, new_lhs, loc, ctx, true)?;

        // get type(lhs).max
        let max_conc = lhs.ty_max_concrete(self).into_expr_err(loc)?.unwrap();
        let max = self.add_concrete_var(ctx, max_conc, loc)?;

        // require lhs + rhs <= type(lhs).max
        if self
            .require(
                arena,
                ctx,
                tmp_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                max,
                RangeOp::Lte,
                ErrType::arithmetic(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // If x and y are signed ints, we have to check that x + -y >= type(x).min
        // because it could overflow in the negative direction
        let lhs_is_int = lhs.is_int(self).into_expr_err(loc)?;
        let rhs_is_int = rhs.is_int(self).into_expr_err(loc)?;
        if lhs_is_int && rhs_is_int {
            let rhs_min_is_negative = rhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(false, self, arena)
                .into_expr_err(loc)?;
            if rhs_min_is_negative {
                // rhs can be negative, require that lhs + rhs >= type(x).min
                // get the lhs min
                let min_conc = lhs.ty_min_concrete(self).into_expr_err(loc)?.unwrap();
                let min = self.add_concrete_var(ctx, min_conc, loc)?;

                if self
                    .require(
                        arena,
                        ctx,
                        new_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                        min,
                        RangeOp::Gte,
                        ErrType::arithmetic(),
                        loc,
                    )?
                    .is_none()
                {
                    return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
                }
            }
        }

        Ok(None)
    }

    fn checked_require_mul(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        lhs: ContextVarNode,
        new_lhs: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        // lhs * rhs <= type(lhs).max
        let new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);
        let tmp_lhs = self.advance_var_in_ctx_forcible(arena, new_lhs, loc, ctx, true)?;

        // get type(lhs).max
        let max_conc = lhs.ty_max_concrete(self).into_expr_err(loc)?.unwrap();
        let max = self.add_concrete_var(ctx, max_conc, loc)?;

        // require lhs * rhs <= type(lhs).max
        if self
            .require(
                arena,
                ctx,
                tmp_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                max,
                RangeOp::Lte,
                ErrType::arithmetic(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // If x and y are signed ints, we have to check that x * -y >= type(x).min
        // because it could overflow in the negative direction
        let lhs_is_int = lhs.is_int(self).into_expr_err(loc)?;
        let rhs_is_int = rhs.is_int(self).into_expr_err(loc)?;
        if lhs_is_int || rhs_is_int {
            let rhs_min_is_negative = rhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(false, self, arena)
                .into_expr_err(loc)?;
            let lhs_min_is_negative = lhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(false, self, arena)
                .into_expr_err(loc)?;
            let rhs_max_is_positive = !rhs
                .evaled_range_max(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(true, self, arena)
                .into_expr_err(loc)?;
            let lhs_max_is_positive = !lhs
                .evaled_range_max(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(true, self, arena)
                .into_expr_err(loc)?;

            let can_go_very_negative = lhs_min_is_negative && rhs_max_is_positive
                || rhs_min_is_negative && lhs_max_is_positive;
            if can_go_very_negative {
                // signs can be opposite so require that lhs * rhs >= type(x).min
                // get the lhs min
                let min_conc = lhs.ty_min_concrete(self).into_expr_err(loc)?.unwrap();
                let min = self.add_concrete_var(ctx, min_conc, loc)?;

                if self
                    .require(
                        arena,
                        ctx,
                        new_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                        min,
                        RangeOp::Gte,
                        ErrType::arithmetic(),
                        loc,
                    )?
                    .is_none()
                {
                    return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
                }
            }
        }

        Ok(None)
    }

    fn checked_require_exp(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        lhs: ContextVarNode,
        new_lhs: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Option<ExprRet>, ExprErr> {
        // exponent must be greater or equal to zero
        let zero = rhs.ty_zero_concrete(self).into_expr_err(loc)?.unwrap();
        let zero = self.add_concrete_var(ctx, zero, loc)?;
        if self
            .require(
                arena,
                ctx,
                rhs,
                zero,
                RangeOp::Gte,
                ErrType::arithmetic(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // lhs ** rhs <= type(lhs).max
        let new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);
        let tmp_lhs = self.advance_var_in_ctx_forcible(arena, new_lhs, loc, ctx, true)?;

        // get type(lhs).max
        let max_conc = lhs.ty_max_concrete(self).into_expr_err(loc)?.unwrap();
        let max = self.add_concrete_var(ctx, max_conc, loc)?;

        // require lhs ** rhs <= type(lhs).max
        if self
            .require(
                arena,
                ctx,
                tmp_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                max,
                RangeOp::Lte,
                ErrType::arithmetic(),
                loc,
            )?
            .is_none()
        {
            return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
        }

        // If x is signed int, we have to check that x ** y >= type(x).min
        // because it could overflow in the negative direction
        let lhs_is_int = lhs.is_int(self).into_expr_err(loc)?;
        if lhs_is_int {
            let lhs_min_is_negative = lhs
                .evaled_range_min(self, arena)
                .into_expr_err(loc)?
                .expect("No range?")
                .is_negative(false, self, arena)
                .into_expr_err(loc)?;
            if lhs_min_is_negative {
                // rhs can be negative, require that lhs + rhs >= type(x).min
                // get the lhs min
                let min_conc = lhs.ty_min_concrete(self).into_expr_err(loc)?.unwrap();
                let min = self.add_concrete_var(ctx, min_conc, loc)?;

                if self
                    .require(
                        arena,
                        ctx,
                        new_lhs.latest_version_or_inherited_in_ctx(ctx, self),
                        min,
                        RangeOp::Gte,
                        ErrType::arithmetic(),
                        loc,
                    )?
                    .is_none()
                {
                    return Ok(Some(ExprRet::CtxKilled(KilledKind::Revert)));
                }
            }
        }

        Ok(None)
    }
}
