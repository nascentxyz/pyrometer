use crate::{context::ContextBuilder, ExprRet};
use ethers_core::types::{I256, U256};
use shared::range::elem::RangeElem;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::{BuiltInNode, Builtin, Concrete, VarType},
    range::{
        elem::RangeOp,
        elem_ty::{Dynamic, Elem},
        Range, RangeEval, SolcRange,
    },
    Edge, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> BinOp for T where T: AnalyzerLike<Expr = Expression> + Sized {}
pub trait BinOp: AnalyzerLike<Expr = Expression> + Sized {
    /// Evaluate and execute a binary operation expression
    fn op_expr(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx);
        match (lhs_paths, rhs_paths) {
            (ExprRet::SingleLiteral((lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                lhs_cvar.try_increase_size(self);
                rhs_cvar.try_increase_size(self);
                let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                if lhs_ctx != rhs_ctx {
                    ExprRet::Multi(vec![
                        all_vars,
                        self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                    ])
                } else {
                    all_vars
                }
            }
            (ExprRet::SingleLiteral((lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                ContextVarNode::from(lhs).cast_from(&ContextVarNode::from(rhs), self);
                let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                if lhs_ctx != rhs_ctx {
                    ExprRet::Multi(vec![
                        all_vars,
                        self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                    ])
                } else {
                    all_vars
                }
            }
            (ExprRet::Single((lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                ContextVarNode::from(rhs).cast_from(&ContextVarNode::from(lhs), self);
                let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                if lhs_ctx != rhs_ctx {
                    ExprRet::Multi(vec![
                        all_vars,
                        self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                    ])
                } else {
                    all_vars
                }
            }
            (ExprRet::Single((lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                if lhs_ctx != rhs_ctx {
                    ExprRet::Multi(vec![
                        all_vars,
                        self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                    ])
                } else {
                    all_vars
                }
            }
            (ExprRet::Single((lhs_ctx, lhs)), ExprRet::Multi(rhs_sides)) => ExprRet::Multi(
                rhs_sides
                    .iter()
                    .map(|expr_ret| {
                        let (rhs_ctx, rhs) = expr_ret.expect_single();
                        let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                        let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                        let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                        if lhs_ctx != rhs_ctx {
                            ExprRet::Multi(vec![
                                all_vars,
                                self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                            ])
                        } else {
                            all_vars
                        }
                    })
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), ExprRet::Single((rhs_ctx, rhs))) => ExprRet::Multi(
                lhs_sides
                    .iter()
                    .map(|expr_ret| {
                        let (lhs_ctx, lhs) = expr_ret.expect_single();
                        let lhs_cvar = ContextVarNode::from(lhs).latest_version(self);
                        let rhs_cvar = ContextVarNode::from(rhs).latest_version(self);
                        let all_vars = self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign);
                        if lhs_ctx != rhs_ctx {
                            ExprRet::Multi(vec![
                                all_vars,
                                self.op(loc, lhs_cvar, rhs_cvar, rhs_ctx, op, assign),
                            ])
                        } else {
                            all_vars
                        }
                    })
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                todo!("here: {lhs_sides:?} {rhs_sides:?}")
            }
            (_, ExprRet::CtxKilled) => ExprRet::CtxKilled,
            (ExprRet::CtxKilled, _) => ExprRet::CtxKilled,
            (l, r) => todo!("here: {l:?} {r:?}"),
        }
    }

    /// Execute a binary operation after parsing the expressions
    fn op(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> ExprRet {
        // println!("op: {:?}, {:?} {:?}", op, lhs_cvar.display_name(self), rhs_cvar.display_name(self));
        let new_lhs = if assign {
            self.advance_var_in_ctx(lhs_cvar, loc, ctx)
        } else {
            let mut new_lhs_underlying = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self),
                    lhs_cvar.name(self),
                    op.to_string(),
                    rhs_cvar.name(self)
                ),
                display_name: format!(
                    "({} {} {})",
                    lhs_cvar.display_name(self),
                    op.to_string(),
                    rhs_cvar.display_name(self)
                ),
                storage: None,
                is_tmp: true,
                is_symbolic: lhs_cvar.is_symbolic(self) || rhs_cvar.is_symbolic(self),
                tmp_of: Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar))),
                ty: lhs_cvar.underlying(self).ty.clone(),
            };

            // will potentially mutate the ty from concrete to builtin with a concrete range
            new_lhs_underlying.ty.concrete_to_builtin(self);

            let new_var = self.add_node(Node::ContextVar(new_lhs_underlying));
            self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
            ContextVarNode::from(new_var)
        };

        let mut new_rhs = rhs_cvar.latest_version(self);

        // TODO: change to only hit this path if !uncheck

        // TODO: If one of lhs_cvar OR rhs_cvar are not symbolic,
        // apply the requirement on the symbolic expression side instead of
        // ignoring the case where

        // if lhs_cvar.is_symbolic(self) && new_rhs.is_symbolic(self) {
        if !assign {
            match op {
                RangeOp::Div | RangeOp::Mod => {
                    if new_rhs.is_const(self) {
                        if new_rhs
                            .evaled_range_min(self)
                            .expect("No range?")
                            .range_eq(&Elem::from(Concrete::from(U256::zero())))
                        {
                            ctx.kill(self, loc);
                            return ExprRet::CtxKilled;
                        }
                    } else if new_rhs.is_symbolic(self) {
                        println!(
                            "lhs: {}, op: {}, rhs: {:?}",
                            lhs_cvar.display_name(self),
                            op.to_string(),
                            new_rhs.display_name(self)
                        );
                        let tmp_rhs = self.advance_var_in_ctx(new_rhs, loc, ctx);
                        let zero_node = self.add_node(Node::Concrete(Concrete::from(U256::zero())));
                        let zero_node = self.add_node(Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, zero_node.into(), self),
                        ));

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!("tmp{}({} != 0)", ctx.new_tmp(self), tmp_rhs.name(self),),
                            display_name: format!("({} != 0)", tmp_rhs.display_name(self),),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                new_lhs,
                                RangeOp::Gt,
                                Some(zero_node.into()),
                            )),
                            is_symbolic: true,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self);

                        let range = tmp_rhs.range(self).expect("No range?");
                        if range.min_is_negative(self) {
                            let mut range_excls = range.range_exclusions();
                            let excl = Elem::from(Concrete::from(I256::zero()));
                            range_excls.push(excl);
                            tmp_rhs.set_range_exclusions(self, range_excls);
                        } else {
                            // the new min is max(1, rhs.min)
                            let min = Elem::max(
                                tmp_rhs.range_min(self).expect("No range minimum?"),
                                Elem::from(Concrete::from(U256::from(1)))
                                    .cast(tmp_rhs.range_min(self).expect("No range minimum?")),
                            );

                            tmp_rhs.set_range_min(self, min);
                            new_rhs = tmp_rhs;
                        }
                    }
                }
                RangeOp::Sub => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_const(self) {
                        if !lhs_cvar.is_int(self) {
                            if let (Some(lmax), Some(rmin)) = (
                                lhs_cvar.evaled_range_max(self),
                                rhs_cvar.evaled_range_min(self),
                            ) {
                                if matches!(
                                    lmax.range_ord(&rmin),
                                    Some(std::cmp::Ordering::Less)
                                        | Some(std::cmp::Ordering::Equal)
                                ) {
                                    ctx.kill(self, loc);
                                    return ExprRet::CtxKilled;
                                }
                            }
                        }
                    } else if lhs_cvar.is_symbolic(self) {
                        let tmp_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx);
                        // the new min is max(lhs.min, rhs.min)
                        let min = Elem::max(
                            tmp_lhs.range_min(self).expect("No range minimum?"),
                            Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc)),
                        );
                        tmp_lhs.set_range_min(self, min);

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} >= {})",
                                ctx.new_tmp(self),
                                tmp_lhs.name(self),
                                new_rhs.name(self),
                            ),
                            display_name: format!(
                                "({} >= {})",
                                tmp_lhs.display_name(self),
                                new_rhs.display_name(self),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Gte,
                                Some(new_rhs),
                            )),
                            is_symbolic: true,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self);
                    }
                }
                RangeOp::Add => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_symbolic(self) {
                        let tmp_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx);

                        // the new max is min(lhs.max, (2**256 - rhs.min))
                        let max = Elem::min(
                            tmp_lhs.range_max(self).expect("No range max?"),
                            Elem::from(Concrete::from(U256::MAX))
                                - Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc)),
                        );

                        tmp_lhs.set_range_max(self, max);

                        let max_node = self.add_node(Node::Concrete(Concrete::from(U256::MAX)));
                        let max_node = self.add_node(Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, max_node.into(), self),
                        ));

                        let (_, tmp_rhs) = self
                            .op(loc, max_node.into(), new_rhs, ctx, RangeOp::Sub, false)
                            .expect_single();

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} <= 2**256 - 1 - {})",
                                ctx.new_tmp(self),
                                tmp_lhs.name(self),
                                new_rhs.name(self),
                            ),
                            display_name: format!(
                                "({} <= 2**256 - 1 - {})",
                                tmp_lhs.display_name(self),
                                new_rhs.display_name(self),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Lte,
                                Some(tmp_rhs.into()),
                            )),
                            is_symbolic: true,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self);
                    }
                }
                RangeOp::Mul => {
                    let lhs_cvar = lhs_cvar.latest_version(self);
                    if lhs_cvar.is_symbolic(self) {
                        let tmp_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx);

                        // the new max is min(lhs.max, (2**256 / max(1, rhs.min)))
                        let max = Elem::min(
                            tmp_lhs.range_max(self).expect("No range max?"),
                            Elem::from(Concrete::from(U256::MAX))
                                / Elem::max(
                                    Elem::from(Concrete::from(U256::from(1))),
                                    Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc)),
                                ),
                        );

                        tmp_lhs.set_range_max(self, max);

                        let max_node = self.add_node(Node::Concrete(Concrete::from(U256::MAX)));
                        let max_node = self.add_node(Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, max_node.into(), self),
                        ));

                        let (_, tmp_rhs) = self
                            .op(loc, max_node.into(), new_rhs, ctx, RangeOp::Div, true)
                            .expect_single();

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} <= (2**256 - 1) / {})",
                                ctx.new_tmp(self),
                                tmp_lhs.name(self),
                                new_rhs.name(self),
                            ),
                            display_name: format!(
                                "({} <= (2**256 - 1) / {})",
                                tmp_lhs.display_name(self),
                                new_rhs.display_name(self),
                            ),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_lhs,
                                RangeOp::Lte,
                                Some(tmp_rhs.into()),
                            )),
                            is_symbolic: true,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self);
                    }
                }
                RangeOp::Exp => {
                    if new_rhs.is_const(self) {
                        if matches!(
                            new_rhs
                                .evaled_range_min(self)
                                .expect("No range")
                                .range_ord(&Elem::from(Concrete::from(U256::zero()))),
                            Some(std::cmp::Ordering::Less)
                        ) {
                            ctx.kill(self, loc);
                            return ExprRet::CtxKilled;
                        }
                    } else if new_rhs.is_symbolic(self) {
                        let tmp_rhs = self.advance_var_in_ctx(rhs_cvar, loc, ctx);
                        // the new min is max(lhs.min, rhs.min)
                        let min = Elem::max(
                            tmp_rhs.range_min(self).expect("No range minimum?"),
                            Elem::from(Concrete::from(U256::zero())),
                        );

                        tmp_rhs.set_range_min(self, min);

                        let zero_node = self.add_node(Node::Concrete(Concrete::from(U256::zero())));
                        let zero_node = self.add_node(Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, zero_node.into(), self),
                        ));

                        let tmp_var = ContextVar {
                            loc: Some(loc),
                            name: format!("tmp{}({} >= 0)", ctx.new_tmp(self), tmp_rhs.name(self),),
                            display_name: format!("({} >= 0)", tmp_rhs.display_name(self),),
                            storage: None,
                            is_tmp: true,
                            tmp_of: Some(TmpConstruction::new(
                                tmp_rhs,
                                RangeOp::Gte,
                                Some(zero_node.into()),
                            )),
                            is_symbolic: true,
                            ty: VarType::BuiltIn(
                                BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                                SolcRange::from(Concrete::Bool(true)),
                            ),
                        };

                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
                        ctx.add_ctx_dep(cvar, self);
                        new_rhs = tmp_rhs;
                    }
                }
                _ => {}
            }
        }

        let lhs_range = if let Some(lhs_range) = new_lhs.range(self) {
            lhs_range
        } else {
            new_rhs
                .range(self)
                .expect("Neither lhs nor rhs had a usable range")
        };

        let func = SolcRange::dyn_fn_from_op(op);
        let new_range = func(lhs_range, new_rhs, loc);
        new_lhs.set_range_min(self, new_range.range_min());
        new_lhs.set_range_max(self, new_range.range_max());

        // last ditch effort to prevent exponentiation from having a minimum of 1 instead of 0.
        // if the lhs is 0 check if the rhs is also 0, otherwise set minimum to 0.
        if matches!(op, RangeOp::Exp) {
            if let (Some(old_lhs_range), Some(rhs_range)) = (
                lhs_cvar.latest_version(self).range(self),
                new_rhs.range(self),
            ) {
                let zero = Elem::from(Concrete::from(U256::zero()));
                let zero_range = SolcRange {
                    min: zero.clone(),
                    max: zero.clone(),
                    exclusions: vec![],
                };
                // We have to check if the the lhs and the right hand side contain the zero range.
                // If they both do, we have to set the minimum to zero due to 0**0 = 1, but 0**x = 0.
                // This is technically a slight widening of the interval and could be improved.
                if old_lhs_range.contains(&zero_range, self)
                    && rhs_range.contains(&zero_range, self)
                {
                    new_lhs.set_range_min(self, zero);
                }
            }
        }
        ExprRet::Single((ctx, new_lhs.into()))
    }
}
