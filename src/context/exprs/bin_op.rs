use crate::context::ContextBuilder;
use crate::ExprRet;
use shared::context::*;
use shared::range::elem::RangeOp;
use shared::range::Range;
use shared::range::SolcRange;
use shared::{analyzer::AnalyzerLike, Edge, Node};
use std::collections::BTreeMap;

use solang_parser::pt::{Expression, Loc};

impl<T> BinOp for T where T: AnalyzerLike + Sized {}
pub trait BinOp: AnalyzerLike + Sized {
    fn op_expr(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(&lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(&rhs_expr, ctx);
        match (lhs_paths, rhs_paths) {
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
            (ExprRet::Multi(_lhs_sides), ExprRet::Multi(_rhs_sides)) => {
                todo!("here")
            }
            (_, ExprRet::CtxKilled) => ExprRet::CtxKilled,
            (ExprRet::CtxKilled, _) => ExprRet::CtxKilled,
            (_, _) => todo!(),
        }
        // lhs_paths.into_iter().flat_map(|lhs_expr_ret| {
        //     let (lhs_ctx, lhs) = lhs_expr_ret.expect_single();
        //     rhs_paths.iter().flat_map(|rhs_expr_ret| {
        //         let (rhs_ctx, rhs) = rhs_expr_ret.expect_single();
        //         let lhs_cvar = ContextVarNode::from(lhs);
        //         let rhs_cvar = ContextVarNode::from(*rhs);
        //         let mut all_vars = vec![self.op(loc, lhs_cvar, rhs_cvar, lhs_ctx, op, assign)];
        //         if lhs_ctx != *rhs_ctx {
        //             all_vars.push(self.op(loc, lhs_cvar, rhs_cvar, *rhs_ctx, op, assign));
        //         }
        //         all_vars
        //     }).collect::<Vec<ExprRet>>()
        // }).collect::<Vec<ExprRet>>()
    }

    fn op(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        op: RangeOp,
        assign: bool,
    ) -> ExprRet {
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
                tmp_of: Some(TmpConstruction::new(lhs_cvar, op, Some(rhs_cvar))),
                ty: lhs_cvar.underlying(self).ty.clone(),
            };

            // will potentially mutate the ty from concrete to builtin with a concrete range
            new_lhs_underlying.ty.concrete_to_builtin(self);

            let new_var = self.add_node(Node::ContextVar(new_lhs_underlying));
            self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
            ContextVarNode::from(new_var)
        };

        let lhs_range = if let Some(lhs_range) = new_lhs.range(self) {
            lhs_range
        } else {
            rhs_cvar
                .range(self)
                .expect("Neither lhs nor rhs had a usable range")
        };

        let (func, range_sides) = SolcRange::dyn_fn_from_op(op);
        let new_range = func(lhs_range, rhs_cvar, range_sides, loc);
        new_lhs.set_range_min(self, new_range.range_min());
        new_lhs.set_range_max(self, new_range.range_max());
        ExprRet::Single((ctx, new_lhs.into()))
    }
}
