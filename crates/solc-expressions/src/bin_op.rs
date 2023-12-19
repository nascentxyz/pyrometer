use crate::{
    require::Require, variable::Variable, ContextBuilder, ExprErr, ExpressionParser, IntoExprErr,
};

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        KilledKind, TmpConstruction,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, Range, RangeEval, SolcRange, VarType,
};

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> BinOp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles binary operations (`+`, `-`, `/`, etc.)
pub trait BinOp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Evaluate and execute a binary operation expression
    #[tracing::instrument(level = "trace", skip_all)]
    fn op_expr(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(rhs_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Binary operation had no right hand side".to_string()))
            };
            if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            let rhs_paths = rhs_paths.flatten();
            let rhs_ctx = ctx;
            analyzer.parse_ctx_expr(lhs_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, format!("Binary operation had no left hand side, Expr: {lhs_expr:#?}, rhs ctx: {}, curr ctx: {}", rhs_ctx.path(analyzer), ctx.path(analyzer))))
                };
                if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                let lhs_paths = lhs_paths.flatten();
                analyzer.op_match(ctx, loc, &lhs_paths, &rhs_paths, op, assign)
            })
        })
    }

    fn op_match(
        &mut self,
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
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                lhs_cvar.try_increase_size(self).into_expr_err(loc)?;
                rhs_cvar.try_increase_size(self).into_expr_err(loc)?;
                ctx.push_expr(self.op(loc, lhs_cvar, rhs_cvar, ctx, op, assign)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::SingleLiteral(lhs), ExprRet::Single(rhs)) => {
                ContextVarNode::from(*lhs)
                    .cast_from(&ContextVarNode::from(*rhs), self)
                    .into_expr_err(loc)?;
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                ctx.push_expr(self.op(loc, lhs_cvar, rhs_cvar, ctx, op, assign)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                ContextVarNode::from(*rhs)
                    .cast_from(&ContextVarNode::from(*lhs), self)
                    .into_expr_err(loc)?;
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                ctx.push_expr(self.op(loc, lhs_cvar, rhs_cvar, ctx, op, assign)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                ctx.push_expr(self.op(loc, lhs_cvar, rhs_cvar, ctx, op, assign)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (lhs @ ExprRet::Single(..), ExprRet::Multi(rhs_sides)) => {
                rhs_sides
                    .iter()
                    .map(|expr_ret| self.op_match(ctx, loc, lhs, expr_ret, op, assign))
                    .collect::<Result<Vec<()>, ExprErr>>()?;
                Ok(())
            }
            (ExprRet::Multi(lhs_sides), rhs @ ExprRet::Single(..)) => {
                lhs_sides
                    .iter()
                    .map(|expr_ret| self.op_match(ctx, loc, expr_ret, rhs, op, assign))
                    .collect::<Result<Vec<()>, ExprErr>>()?;
                Ok(())
            }
            (_, ExprRet::CtxKilled(kind)) => ctx.kill(self, loc, *kind).into_expr_err(loc),
            (ExprRet::CtxKilled(kind), _) => ctx.kill(self, loc, *kind).into_expr_err(loc),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled combination in binop: {lhs_sides:?} {rhs_sides:?}"),
            )),
            (l, r) => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled combination in binop: {l:?} {r:?}"),
            )),
        }
    }

    /// Execute a binary operation after parsing the expressions
    #[tracing::instrument(level = "trace", skip_all)]
    fn op(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "binary op: {} {} {}, assign: {}",
            lhs_cvar.display_name(self).into_expr_err(loc)?,
            op.to_string(),
            rhs_cvar.display_name(self).into_expr_err(loc)?,
            assign
        );

        let unchecked = match op {
            RangeOp::Add(u) | RangeOp::Sub(u) | RangeOp::Mul(u) | RangeOp::Div(u) => u,
            _ => false,
        };

        let new_lhs = if assign {
            let new = self.advance_var_in_ctx_forcible(lhs_cvar, loc, ctx, true)?;
            new.underlying_mut(self).into_expr_err(loc)?.tmp_of =
                Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar)));
            new
        } else {
            let mut new_lhs_underlying = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self).into_expr_err(loc)?,
                    lhs_cvar.name(self).into_expr_err(loc)?,
                    op.to_string(),
                    rhs_cvar.name(self).into_expr_err(loc)?
                ),
                display_name: format!(
                    "({} {} {})",
                    lhs_cvar.display_name(self).into_expr_err(loc)?,
                    op.to_string(),
                    rhs_cvar.display_name(self).into_expr_err(loc)?
                ),
                storage: None,
                is_tmp: true,
                is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?
                    || rhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                is_return: false,
                tmp_of: Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar))),
                ty: lhs_cvar.underlying(self).into_expr_err(loc)?.ty.clone(),
            };

            // will potentially mutate the ty from concrete to builtin with a concrete range
            new_lhs_underlying
                .ty
                .concrete_to_builtin(self)
                .into_expr_err(loc)?;

            let new_var = self.add_node(Node::ContextVar(new_lhs_underlying));
            ctx.add_var(new_var.into(), self).into_expr_err(loc)?;
            self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
            ContextVarNode::from(new_var)
        };

        let mut new_rhs = rhs_cvar.latest_version(self);

        let expr = Elem::Expr(RangeExpr::<Concrete>::new(
            Elem::from(Reference::new(lhs_cvar.latest_version(self).into())),
            op,
            Elem::from(Reference::new(rhs_cvar.latest_version(self).into())),
        ));

        // to prevent some recursive referencing, forcibly increase lhs_cvar
        self.advance_var_in_ctx_forcible(lhs_cvar.latest_version(self), loc, ctx, true)?;

        // TODO: If one of lhs_cvar OR rhs_cvar are not symbolic,
        // apply the requirement on the symbolic expression side instead of
        // ignoring the case where

        // if lhs_cvar.is_symbolic(self) && new_rhs.is_symbolic(self) {
        if !unchecked {
            match op {
                RangeOp::Div(..) | RangeOp::Mod => {
                    // x / y

                    if new_rhs.is_const(self).into_expr_err(loc)? {
                        // y is constant, do a check if it is 0
                        if new_rhs
                            .evaled_range_min(self)
                            .into_expr_err(loc)?
                            .expect("No range?")
                            .range_eq(&Elem::from(Concrete::from(U256::zero())))
                        {
                            let res = ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc);
                            let _ = self.add_if_err(res);

                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }
                    } else if new_rhs.is_symbolic(self).into_expr_err(loc)? {
                        // y is symbolic, add
                        let tmp_rhs = self.advance_var_in_ctx(new_rhs, loc, ctx)?;
                        let zero_node = self.add_node(Node::Concrete(Concrete::from(U256::zero())));
                        let var = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            zero_node.into(),
                            self,
                        );
                        let zero_node = self.add_node(Node::ContextVar(var.into_expr_err(loc)?));

                        if self
                            .require(
                                tmp_rhs,
                                zero_node.into(),
                                ctx,
                                loc,
                                RangeOp::Neq,
                                RangeOp::Eq,
                                (RangeOp::Eq, RangeOp::Neq),
                            )?
                            .is_none()
                        {
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }

                        // let tmp_rhs = tmp_rhs.latest_version(self);

                        // let tmp_var = ContextVar {
                        //     loc: Some(loc),
                        //     name: format!(
                        //         "tmp{}({} != 0)",
                        //         ctx.new_tmp(self).into_expr_err(loc)?,
                        //         tmp_rhs.name(self).into_expr_err(loc)?,
                        //     ),
                        //     display_name: format!(
                        //         "({} != 0)",
                        //         tmp_rhs.display_name(self).into_expr_err(loc)?,
                        //     ),
                        //     storage: None,
                        //     is_tmp: true,
                        //     tmp_of: Some(TmpConstruction::new(
                        //         new_lhs,
                        //         RangeOp::Neq,
                        //         Some(zero_node.into()),
                        //     )),
                        //     is_symbolic: true,
                        //     is_return: false,
                        //     ty: VarType::BuiltIn(
                        //         BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        //         SolcRange::from(Concrete::Bool(true)),
                        //     ),
                        // };

                        // let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        // ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;

                        // let range = tmp_rhs
                        //     .ref_range(self)
                        //     .into_expr_err(loc)?
                        //     .expect("No range?");
                        // if range.min_is_negative(self).into_expr_err(loc)? {
                        //     let mut range_excls = range.range_exclusions();
                        //     let excl = Elem::from(Concrete::from(I256::zero()));
                        //     if !range_excls.contains(&excl) {
                        //         range_excls.push(excl);
                        //     }
                        //     tmp_rhs
                        //         .set_range_exclusions(self, range_excls)
                        //         .into_expr_err(loc)?;
                        // } else {
                        //     // the new min is max(1, rhs.min)
                        //     let min = Elem::max(
                        //         Elem::from(Reference::new(new_rhs.into())),
                        //         // tmp_rhs
                        //         //     .range_min(self)
                        //         //     .into_expr_err(loc)?
                        //         //     .unwrap_or_else(|| {
                        //         //         panic!("No range minimum: {:?}", tmp_rhs.underlying(self))
                        //         //     }),
                        //         Elem::from(Concrete::from(U256::from(1))).cast(
                        //             Elem::from(Reference::new(tmp_rhs.into())), // .range_min(self)
                        //                                                         // .into_expr_err(loc)?
                        //                                                         // .expect("No range minimum?"),
                        //         ),
                        //     );

                        //     tmp_rhs.set_range_min(self, min).into_expr_err(loc)?;
                        //     new_rhs = tmp_rhs;
                        // }
                    }
                }
                RangeOp::Sub(..) => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_const(self).into_expr_err(loc)? {
                        if !lhs_cvar.is_int(self).into_expr_err(loc)? {
                            if let (Some(lmax), Some(rmin)) = (
                                lhs_cvar.evaled_range_max(self).into_expr_err(loc)?,
                                rhs_cvar.evaled_range_min(self).into_expr_err(loc)?,
                            ) {
                                if matches!(
                                    lmax.range_ord(&rmin),
                                    Some(std::cmp::Ordering::Less)
                                        | Some(std::cmp::Ordering::Equal)
                                ) {
                                    ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;

                                    return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                                }
                            }
                        }
                    } else if lhs_cvar.is_symbolic(self).into_expr_err(loc)? {
                        let tmp_lhs = self.advance_var_in_ctx_forcible(lhs_cvar, loc, ctx, true)?;
                        // let tmp_rhs = self.advance_var_in_ctx_forcible(new_rhs, loc, ctx, true)?;
                        if self
                            .require(
                                tmp_lhs,
                                new_rhs,
                                ctx,
                                loc,
                                RangeOp::Gte,
                                RangeOp::Lte,
                                (RangeOp::Lte, RangeOp::Gte),
                            )?
                            .is_none()
                        {
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }
                        // the new min is max(lhs.min, rhs.min)
                        let min = Elem::max(
                            Elem::from(Reference::new(lhs_cvar.into())),
                            Elem::from(rhs_cvar),
                        );
                        let tmp_lhs = tmp_lhs.latest_version(self);
                        tmp_lhs.set_range_min(self, min).into_expr_err(loc)?;

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} >= {})",
                                ctx.new_tmp(self).into_expr_err(loc)?,
                                tmp_lhs.name(self).into_expr_err(loc)?,
                                new_rhs.name(self).into_expr_err(loc)?,
                            ),
                            display_name: format!(
                                "({} >= {})",
                                tmp_lhs.display_name(self).unwrap(),
                                new_rhs.display_name(self).unwrap(),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Gte,
                                Some(new_rhs),
                            )),
                            is_symbolic: true,
                            is_return: false,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;
                    }
                }
                RangeOp::Add(..) => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_symbolic(self).into_expr_err(loc)? {
                        let tmp_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx)?;

                        // the new max is min(lhs.max, (2**256 - rhs.min))
                        let max = Elem::min(
                            Elem::from(Reference::new(lhs_cvar.into())),
                            // .range_max(self)
                            // .into_expr_err(loc)?
                            // .expect("No range max?"),
                            Elem::from(Concrete::from(U256::MAX)) - Elem::from(rhs_cvar),
                        );

                        tmp_lhs.set_range_max(self, max).into_expr_err(loc)?;

                        let max_node = self.add_node(Node::Concrete(Concrete::from(U256::MAX)));
                        let tmp_max = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            max_node.into(),
                            self,
                        );
                        let max_node = self.add_node(Node::ContextVar(tmp_max.into_expr_err(loc)?));

                        let tmp_rhs = self.op(
                            loc,
                            max_node.into(),
                            new_rhs,
                            ctx,
                            RangeOp::Sub(true),
                            false,
                        )?;

                        if matches!(tmp_rhs, ExprRet::CtxKilled(_)) {
                            return Ok(tmp_rhs);
                        }

                        let tmp_rhs = tmp_rhs.expect_single().into_expr_err(loc)?;

                        if self
                            .require(
                                tmp_lhs,
                                tmp_rhs.into(),
                                ctx,
                                loc,
                                RangeOp::Lte,
                                RangeOp::Gte,
                                (RangeOp::Gte, RangeOp::Lte),
                            )?
                            .is_none()
                        {
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} <= 2**256 - 1 - {})",
                                ctx.new_tmp(self).into_expr_err(loc)?,
                                tmp_lhs.name(self).into_expr_err(loc)?,
                                new_rhs.name(self).into_expr_err(loc)?,
                            ),
                            display_name: format!(
                                "({} <= 2**256 - 1 - {})",
                                tmp_lhs.display_name(self).unwrap(),
                                new_rhs.display_name(self).unwrap(),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Lte,
                                Some(tmp_rhs.into()),
                            )),
                            is_symbolic: true,
                            is_return: false,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;
                    }
                }
                RangeOp::Mul(..) => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_symbolic(self).into_expr_err(loc)? {
                        let tmp_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx)?;

                        // the new max is min(lhs.max, (2**256 / max(1, rhs.min)))
                        let max = Elem::min(
                            Elem::from(Reference::new(lhs_cvar.into())),
                            // .range_max(self)
                            // .into_expr_err(loc)?
                            // .expect("No range max?"),
                            Elem::from(Concrete::from(U256::MAX))
                                / Elem::max(
                                    Elem::from(Concrete::from(U256::from(1))),
                                    Elem::from(rhs_cvar),
                                ),
                        );

                        tmp_lhs.set_range_max(self, max).into_expr_err(loc)?;

                        let max_node = self.add_node(Node::Concrete(Concrete::from(U256::MAX)));
                        let tmp_max = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            max_node.into(),
                            self,
                        );
                        let max_node = self.add_node(Node::ContextVar(tmp_max.into_expr_err(loc)?));

                        let tmp_rhs = self.op(
                            loc,
                            max_node.into(),
                            new_rhs,
                            ctx,
                            RangeOp::Div(true),
                            false,
                        )?;

                        if matches!(tmp_rhs, ExprRet::CtxKilled(_)) {
                            return Ok(tmp_rhs);
                        }

                        let tmp_rhs = tmp_rhs.expect_single().into_expr_err(loc)?;

                        if self
                            .require(
                                tmp_lhs,
                                tmp_rhs.into(),
                                ctx,
                                loc,
                                RangeOp::Lte,
                                RangeOp::Gte,
                                (RangeOp::Gte, RangeOp::Lte),
                            )?
                            .is_none()
                        {
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }

                        let tmp_rhs = ContextVarNode::from(tmp_rhs).latest_version(self);

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} <= (2**256 - 1) / {})",
                                ctx.new_tmp(self).into_expr_err(loc)?,
                                tmp_lhs.name(self).into_expr_err(loc)?,
                                new_rhs.name(self).into_expr_err(loc)?,
                            ),
                            display_name: format!(
                                "({} <= (2**256 - 1) / {})",
                                tmp_lhs.display_name(self).unwrap(),
                                new_rhs.display_name(self).unwrap(),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Lte,
                                Some(tmp_rhs),
                            )),
                            is_symbolic: true,
                            is_return: false,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;
                    }
                }
                RangeOp::Exp => {
                    if new_rhs.is_const(self).into_expr_err(loc)? {
                        if matches!(
                            new_rhs
                                .evaled_range_min(self)
                                .into_expr_err(loc)?
                                .expect("No range")
                                .range_ord(&Elem::from(Concrete::from(U256::zero()))),
                            Some(std::cmp::Ordering::Less)
                        ) {
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }
                    } else if new_rhs.is_symbolic(self).into_expr_err(loc)? {
                        let tmp_rhs = self.advance_var_in_ctx(rhs_cvar, loc, ctx)?;
                        // the new min is max(lhs.min, rhs.min)
                        let min = Elem::max(
                            Elem::from(Reference::new(rhs_cvar.into())),
                            // .range_min(self)
                            // .into_expr_err(loc)?
                            // .expect("No range minimum?"),
                            Elem::from(Concrete::from(U256::zero())),
                        );

                        tmp_rhs.set_range_min(self, min).into_expr_err(loc)?;

                        let zero_node = self.add_node(Node::Concrete(Concrete::from(U256::zero())));
                        let tmp_zero = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            zero_node.into(),
                            self,
                        );
                        let zero_node =
                            self.add_node(Node::ContextVar(tmp_zero.into_expr_err(loc)?));

                        if self
                            .require(
                                tmp_rhs,
                                zero_node.into(),
                                ctx,
                                loc,
                                RangeOp::Gte,
                                RangeOp::Lte,
                                (RangeOp::Lte, RangeOp::Gte),
                            )?
                            .is_none()
                        {
                            return Ok(ExprRet::CtxKilled(KilledKind::Revert));
                        }

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} >= 0)",
                                ctx.new_tmp(self).into_expr_err(loc)?,
                                tmp_rhs.name(self).into_expr_err(loc)?,
                            ),
                            display_name: format!(
                                "({} >= 0)",
                                tmp_rhs.display_name(self).into_expr_err(loc)?,
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_rhs,
                                RangeOp::Gte,
                                Some(zero_node.into()),
                            )),
                            is_symbolic: true,
                            is_return: false,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;
                        new_rhs = tmp_rhs;
                    }
                }
                _ => {}
            }
        } else {

            // self.advance_var_in_ctx_forcible(rhs_cvar.latest_version(self), loc, ctx, true)?;
        }

        // let lhs_range = if let Some(lhs_range) = new_lhs.range(self).into_expr_err(loc)? {
        //     lhs_range
        // } else {
        //     new_rhs
        //         .range(self)
        //         .into_expr_err(loc)?
        //         .expect("Neither lhs nor rhs had a usable range")
        // };

        // let func = SolcRange::dyn_fn_from_op(op);
        // let new_range = func(lhs_range, new_rhs);
        new_lhs
            .latest_version(self)
            .set_range_min(self, expr.clone())
            .into_expr_err(loc)?;
        new_lhs
            .latest_version(self)
            .set_range_max(self, expr)
            .into_expr_err(loc)?;

        // last ditch effort to prevent exponentiation from having a minimum of 1 instead of 0.
        // if the lhs is 0 check if the rhs is also 0, otherwise set minimum to 0.
        if matches!(op, RangeOp::Exp) {
            if let (Some(old_lhs_range), Some(rhs_range)) = (
                lhs_cvar
                    .latest_version(self)
                    .ref_range(self)
                    .into_expr_err(loc)?,
                new_rhs.ref_range(self).into_expr_err(loc)?,
            ) {
                let zero = Elem::from(Concrete::from(U256::zero()));
                let zero_range = SolcRange::new(zero.clone(), zero.clone(), vec![]);
                // We have to check if the the lhs and the right hand side contain the zero range.
                // If they both do, we have to set the minimum to zero due to 0**0 = 1, but 0**x = 0.
                // This is technically a slight widening of the interval and could be improved.
                if old_lhs_range.contains(&zero_range, self)
                    && rhs_range.contains(&zero_range, self)
                {
                    new_lhs.set_range_min(self, zero).into_expr_err(loc)?;
                }
            }
        }
        Ok(ExprRet::Single(new_lhs.latest_version(self).into()))
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn bit_not(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
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
            analyzer.bit_not_inner(ctx, loc, lhs.flatten())
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn bit_not_inner(
        &mut self,
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
            ExprRet::SingleLiteral(lhs) => {
                // TODO: try to pop from the stack and if there is a single element there
                // use it as a type hint, then place it back on the stack
                ContextVarNode::from(lhs)
                    .try_increase_size(self)
                    .into_expr_err(loc)?;
                self.bit_not_inner(ctx, loc, ExprRet::Single(lhs))?;
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
                    is_symbolic: lhs_cvar.is_symbolic(self).into_expr_err(loc)?,
                    is_return: false,
                    ty: lhs_cvar.underlying(self).into_expr_err(loc)?.ty.clone(),
                };

                let expr = Elem::Expr(RangeExpr::<Concrete>::new(
                    Elem::from(Reference::new(lhs_cvar.latest_version(self).into())),
                    RangeOp::BitNot,
                    Elem::Null,
                ));

                let out_var = ContextVarNode::from(self.add_node(Node::ContextVar(out_var)));

                out_var
                    .set_range_min(self, expr.clone())
                    .into_expr_err(loc)?;
                out_var.set_range_max(self, expr).into_expr_err(loc)?;
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
}
