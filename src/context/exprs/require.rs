use crate::context::exprs::cmp::Cmp;
use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{
    exprs::{BinOp, Variable},
    AnalyzerLike, Concrete, ConcreteNode, ContextBuilder, Node,
};
use shared::range::range_string::ToRangeString;

use shared::{
    context::*,
    nodes::{BuiltInNode, Builtin, VarType},
    range::{
        elem::{RangeElem, RangeOp},
        elem_ty::{Elem, RangeConcrete},
        Range, RangeEval, SolcRange,
    },
    Edge,
};
use solang_parser::helpers::CodeLocation;

use ethers_core::types::I256;
use solang_parser::pt::{Expression, Loc};
use std::cmp::Ordering;

impl<T> Require for T where T: Variable + BinOp + Sized + AnalyzerLike {}
pub trait Require: AnalyzerLike + Variable + BinOp + Sized {
    /// Handles a require expression
    #[tracing::instrument(level = "trace", skip_all)]
    fn handle_require(&mut self, inputs: &[Expression], ctx: ContextNode) -> Result<(), ExprErr> {
        match inputs.get(0).expect("No lhs input for require statement") {
            Expression::Equal(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `==` had no right hand side".to_string()))
                    };

                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `==` had no left hand side".to_string()))
                        };

                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Eq,
                            RangeOp::Neq,
                            (RangeOp::Neq, RangeOp::Eq),
                        )
                    })
                })
            }
            Expression::NotEqual(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `!=` had no right hand side".to_string()))
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `!=` had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Neq,
                            RangeOp::Eq,
                            (RangeOp::Eq, RangeOp::Neq),
                        )
                    })
                })
            }
            Expression::Less(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `<` had no right hand side".to_string()))
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `<` had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Lt,
                            RangeOp::Gt,
                            (RangeOp::Gt, RangeOp::Lt),
                        )
                    })
                })
            }
            Expression::More(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `>` had no right hand side".to_string()))
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `>` had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Gt,
                            RangeOp::Lt,
                            (RangeOp::Lt, RangeOp::Gt),
                        )
                    })
                })
            }
            Expression::MoreEqual(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `>=` had no right hand side".to_string()))
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `>=` had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Gte,
                            RangeOp::Lte,
                            (RangeOp::Lte, RangeOp::Gte),
                        )
                    })
                })
            }
            Expression::LessEqual(loc, lhs, rhs) => {
                self.parse_ctx_expr(rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Require operation `<=` had no right hand side".to_string()))
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Require operation `<=` had no left hand side".to_string()))
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Lte,
                            RangeOp::Gte,
                            (RangeOp::Gte, RangeOp::Lte),
                        )
                    })
                })
            }
            Expression::Not(loc, lhs) => {
                self.parse_ctx_expr(lhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Require operation `NOT` had no left hand side".to_string()))
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let cnode =
                        ConcreteNode::from(analyzer.add_node(Node::Concrete(Concrete::Bool(false))));
                    let tmp_false = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(loc)?,
                    );
                    let rhs_paths =
                        ExprRet::Single(ContextVarNode::from(analyzer.add_node(tmp_false)).into());
                    analyzer.handle_require_inner(
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Neq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
            Expression::And(loc, lhs, rhs) => {
                self.cmp(*loc, lhs, RangeOp::And, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Require operation `&&` had no left hand side".to_string()))
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let cnode = ConcreteNode::from(analyzer.add_node(Node::Concrete(Concrete::Bool(true))));
                    let tmp_true = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(loc)?,
                    );
                    let node = analyzer.add_node(tmp_true);
                    ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    let rhs_paths = ExprRet::Single(node);

                    analyzer.handle_require_inner(
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Neq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
            Expression::Or(loc, lhs, rhs) => {
                self.cmp(*loc, lhs, RangeOp::Or, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Require operation `||` had no left hand side".to_string()))
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let cnode = ConcreteNode::from(analyzer.add_node(Node::Concrete(Concrete::Bool(true))));
                    let tmp_true = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(loc)?,
                    );
                    let node = analyzer.add_node(tmp_true);
                    ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    let rhs_paths = ExprRet::Single(node);
                    analyzer.handle_require_inner(
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Neq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
            other => {
                self.parse_ctx_expr(other, ctx)?;
                self.apply_to_edges(ctx, other.loc(), &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Require operation had no left hand side".to_string()))
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let cnode = ConcreteNode::from(analyzer.add_node(Node::Concrete(Concrete::Bool(true))));
                    let tmp_true = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(other.loc())?,
                    );
                    let rhs_paths =
                        ExprRet::Single(ContextVarNode::from(analyzer.add_node(tmp_true)).into());
                    analyzer.handle_require_inner(
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Neq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
        }
    }

    fn handle_require_inner(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
        op: RangeOp,
        rhs_op: RangeOp,
        recursion_ops: (RangeOp, RangeOp),
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (_, ExprRet::CtxKilled(..)) | (ExprRet::CtxKilled(..), _) => Ok(()),
            (ExprRet::SingleLiteral(lhs), ExprRet::Single(rhs)) => {
                ContextVarNode::from(*lhs)
                    .cast_from(&ContextVarNode::from(*rhs), self)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    ctx,
                    loc,
                    &ExprRet::Single(*lhs),
                    rhs_paths,
                    op,
                    rhs_op,
                    recursion_ops,
                )
            }
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                ContextVarNode::from(*rhs)
                    .cast_from(&ContextVarNode::from(*lhs), self)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    ctx,
                    loc,
                    lhs_paths,
                    &ExprRet::Single(*rhs),
                    op,
                    rhs_op,
                    recursion_ops,
                )
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx)?;
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, ctx)?;

                self.require(new_lhs, new_rhs, ctx, loc, op, rhs_op, recursion_ops)?;
                Ok(())
            }
            (l @ ExprRet::Single(_) | l @ ExprRet::SingleLiteral(_), ExprRet::Multi(rhs_sides)) => {
                rhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(ctx, loc, l, expr_ret, op, rhs_op, recursion_ops)
                })
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                lhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(ctx, loc, expr_ret, r, op, rhs_op, recursion_ops)
                })
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.handle_require_inner(
                                ctx,
                                loc,
                                lhs_expr_ret,
                                rhs_expr_ret,
                                op,
                                rhs_op,
                                recursion_ops,
                            )
                        },
                    )
                } else {
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.handle_require_inner(
                            ctx,
                            loc,
                            lhs_paths,
                            rhs_expr_ret,
                            op,
                            rhs_op,
                            recursion_ops,
                        )
                    })
                }
            }
            (e, f) => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled combination in require: {:?} {:?}", e, f),
            )),
        }
    }

    /// Updates the range bounds for the variables passed into the require function. If the lefthand side is a temporary value,
    /// it will recursively update the range bounds for the underlying variable
    #[allow(clippy::too_many_arguments)]
    #[tracing::instrument(level = "trace", skip_all)]
    fn require(
        &mut self,
        mut new_lhs: ContextVarNode,
        mut new_rhs: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        op: RangeOp,
        rhs_op: RangeOp,
        recursion_ops: (RangeOp, RangeOp),
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        tracing::trace!(
            "require: {} {} {}",
            new_lhs.display_name(self).into_expr_err(loc)?,
            op.to_string(),
            new_rhs.display_name(self).into_expr_err(loc)?
        );
        let mut any_unsat = false;
        let mut tmp_cvar = None;

        if let Some(lhs_range) = new_lhs
            .underlying(self)
            .into_expr_err(loc)?
            .ty
            .range(self)
            .into_expr_err(loc)?
        {
            let lhs_range_fn = SolcRange::dyn_fn_from_op(op);
            // lhs_range.update_deps(new_lhs, ctx, self);
            let mut new_var_range = lhs_range_fn(lhs_range.clone(), new_rhs);

            if let Some(rhs_range) = new_rhs.range(self).into_expr_err(loc)? {
                let lhs_is_const = new_lhs.is_const(self).into_expr_err(loc)?;
                let rhs_is_const = new_rhs.is_const(self).into_expr_err(loc)?;
                match (lhs_is_const, rhs_is_const) {
                    (true, true) => {
                        if self.const_killable(op, lhs_range, rhs_range) {
                            tracing::trace!("const killable");
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (true, false) => {
                        // flip the new range around to be in terms of rhs
                        let rhs_range_fn = SolcRange::dyn_fn_from_op(rhs_op);
                        new_var_range = rhs_range_fn(rhs_range.clone(), new_lhs);

                        if self
                            .update_nonconst_from_const(loc, rhs_op, new_lhs, new_rhs, rhs_range)?
                        {
                            tracing::trace!("half-const killable");
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, true) => {
                        if self.update_nonconst_from_const(loc, op, new_rhs, new_lhs, lhs_range)? {
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, false) => {
                        if self.update_nonconst_from_nonconst(
                            loc, op, new_lhs, new_rhs, lhs_range, rhs_range,
                        )? {
                            tracing::trace!("nonconst killable");
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

            if let Some(backing_arr) = new_lhs.len_var_to_array(self).into_expr_err(loc)? {
                if let Some(r) = backing_arr.ref_range(self).into_expr_err(loc)? {
                    let min = r.range_min().into_owned();
                    let max = r.range_max().into_owned();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::from(new_lhs);
                        backing_arr
                            .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc)?;
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::from(new_lhs);
                        backing_arr
                            .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc)?;
                    }
                }
            } else if let Some(arr) = new_lhs.index_to_array(self) {
                if let Some(index) = new_lhs.index_access_to_index(self) {
                    let next_arr = self.advance_var_in_ctx(arr.latest_version(self), loc, ctx)?;
                    if next_arr
                        .underlying(self)
                        .into_expr_err(loc)?
                        .ty
                        .is_dyn_builtin(self)
                        .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.val.insert(Elem::from(index), Elem::from(new_rhs));
                                next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc)?;
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.val.insert(Elem::from(index), Elem::from(new_rhs));
                                next_arr
                                    .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc)?;
                            }
                        }
                    }
                }
            }

            if let Some(backing_arr) = new_rhs.len_var_to_array(self).into_expr_err(loc)? {
                if let Some(r) = backing_arr.ref_range(self).into_expr_err(loc)? {
                    let min = r.range_min().into_owned();
                    let max = r.range_max().into_owned();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::from(new_lhs);
                        backing_arr
                            .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc)?;
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::from(new_lhs);
                        backing_arr
                            .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc)?;
                    }
                }
            }

            let tmp_var = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self).into_expr_err(loc)?,
                    new_lhs.name(self).into_expr_err(loc)?,
                    op.to_string(),
                    new_rhs.name(self).into_expr_err(loc)?,
                ),
                display_name: format!(
                    "({} {} {})",
                    new_lhs.display_name(self).into_expr_err(loc)?,
                    op.to_string(),
                    new_rhs.display_name(self).into_expr_err(loc)?,
                ),
                storage: None,
                is_tmp: true,
                tmp_of: Some(TmpConstruction::new(new_lhs, op, Some(new_rhs))),
                is_symbolic: new_lhs.is_symbolic(self).into_expr_err(loc)?
                    || new_rhs.is_symbolic(self).into_expr_err(loc)?,
                is_return: false,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                    SolcRange::from(Concrete::Bool(true)),
                ),
            };

            let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
            ctx.add_var(cvar, self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

            tmp_cvar = Some(cvar);

            any_unsat |= new_var_range.unsat(self);
            if any_unsat {
                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                return Ok(None);
            }

            ctx.add_ctx_dep(cvar, self).into_expr_err(loc)?;
        }

        new_lhs.update_deps(ctx, self).into_expr_err(loc)?;
        new_rhs.update_deps(ctx, self).into_expr_err(loc)?;
        tracing::trace!(
            "{} is tmp: {}",
            new_lhs.display_name(self).unwrap(),
            new_lhs.is_tmp(self).unwrap()
        );
        if let Some(tmp) = new_lhs.tmp_of(self).into_expr_err(loc)? {
            if tmp.op.inverse().is_some() && !matches!(op, RangeOp::Eq | RangeOp::Neq) {
                self.range_recursion(tmp, recursion_ops, new_rhs, ctx, loc, &mut any_unsat)?;
            } else {
                match tmp.op {
                    RangeOp::Not => {}
                    _ => {
                        self.uninvertable_range_recursion(tmp, new_lhs, new_rhs, loc, ctx);
                    }
                }
            }
        }

        Ok(tmp_cvar)
    }

    /// Checks and returns whether the require statement is killable (i.e. impossible)
    fn const_killable(&mut self, op: RangeOp, lhs_range: SolcRange, rhs_range: SolcRange) -> bool {
        // check that the op is satisfied, return it as a bool
        match op {
            RangeOp::Eq => !lhs_range
                .evaled_range_min(self)
                .unwrap()
                .range_eq(&rhs_range.evaled_range_min(self).unwrap()),
            RangeOp::Neq => lhs_range
                .evaled_range_min(self)
                .unwrap()
                .range_eq(&rhs_range.evaled_range_min(self).unwrap()),
            RangeOp::Gt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self).unwrap()),
                    Some(Ordering::Equal) | Some(Ordering::Less)
                )
            }
            RangeOp::Gte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self).unwrap()),
                    Some(Ordering::Less)
                )
            }
            RangeOp::Lt => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self).unwrap()),
                    Some(Ordering::Equal) | Some(Ordering::Greater)
                )
            }
            RangeOp::Lte => {
                matches!(
                    lhs_range
                        .evaled_range_min(self)
                        .unwrap()
                        .range_ord(&rhs_range.evaled_range_min(self).unwrap()),
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
        loc: Loc,
        op: RangeOp,
        const_var: ContextVarNode,
        nonconst_var: ContextVarNode,
        mut nonconst_range: SolcRange,
    ) -> Result<bool, ExprErr> {
        tracing::trace!("Setting range for nonconst from const");
        match op {
            RangeOp::Eq => {
                // check that the constant is contained in the nonconst var range
                let elem = Elem::from(const_var.latest_version(self));
                let evaled_min = nonconst_range.evaled_range_min(self).into_expr_err(loc)?;
                if evaled_min.maybe_concrete().is_none() {
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug. Min: {}", evaled_min.to_range_string(false, self).s)));
                }

                if !nonconst_range.contains_elem(&elem, self) {
                    return Ok(true);
                }
                // if its contained, we can set the min & max to it
                nonconst_var
                    .set_range_min(self, elem.clone())
                    .into_expr_err(loc)?;
                nonconst_var.set_range_max(self, elem).into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Neq => {
                // check if contains
                let elem = Elem::from(const_var.latest_version(self));

                // potentially add the const var as a range exclusion
                if let Some(Ordering::Equal) = nonconst_range
                    .evaled_range_min(self)
                    .into_expr_err(loc)?
                    .range_ord(&elem)
                {
                    // mins are equivalent, add 1 instead of adding an exclusion
                    let Some(min) = nonconst_range
                        .evaled_range_min(self)
                        .into_expr_err(loc)?
                        .maybe_concrete() else {
                        panic!("min: {:?}, max: {:?}", nonconst_range.evaled_range_min(self), nonconst_range.evaled_range_max(self));
                    };
                    let one = Concrete::one(&min.val).expect("Cannot increment range elem by one");
                    let min = nonconst_range.range_min().into_owned() + Elem::from(one);
                    nonconst_var.set_range_min(self, min).into_expr_err(loc)?;
                } else if let Some(std::cmp::Ordering::Equal) = nonconst_range
                    .evaled_range_max(self)
                    .into_expr_err(loc)?
                    .range_ord(&elem)
                {
                    // maxs are equivalent, subtract 1 instead of adding an exclusion
                    let max = nonconst_range
                        .evaled_range_max(self)
                        .into_expr_err(loc)?
                        .maybe_concrete()
                        .expect("Was not concrete");
                    let one = Concrete::one(&max.val).expect("Cannot decrement range elem by one");
                    let max = nonconst_range.range_max().into_owned() - Elem::from(one);
                    nonconst_var.set_range_max(self, max).into_expr_err(loc)?;
                } else {
                    // just add as an exclusion
                    nonconst_range.add_range_exclusion(elem);
                    nonconst_var
                        .set_range_exclusions(self, nonconst_range.exclusions)
                        .into_expr_err(loc)?;
                }

                Ok(false)
            }
            RangeOp::Gt => {
                let elem = Elem::from(const_var.latest_version(self));

                // if nonconst max is <= const, we can't make this true
                let max = nonconst_range.evaled_range_max(self).into_expr_err(loc)?;
                if matches!(
                    max.range_ord(&elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add one to the element because its strict >
                let max_conc = max.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");
                nonconst_var
                    .set_range_min(
                        self,
                        (elem + one.into()).max(nonconst_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Gte => {
                let elem = Elem::from(const_var.latest_version(self));

                // if nonconst max is < const, we can't make this true
                if matches!(
                    nonconst_range
                        .evaled_range_max(self)
                        .into_expr_err(loc)?
                        .range_ord(&elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Less)
                ) {
                    return Ok(true);
                }

                nonconst_var
                    .set_range_min(self, elem.max(nonconst_range.range_min().into_owned()))
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lt => {
                let elem = Elem::from(const_var.latest_version(self));

                // if nonconst min is >= const, we can't make this true
                let min = nonconst_range.evaled_range_min(self).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add one to the element because its strict >
                let min_conc = min.maybe_concrete().expect("Was not concrete");
                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                nonconst_var
                    .set_range_max(
                        self,
                        (elem - one.into()).min(nonconst_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lte => {
                let elem = Elem::from(const_var.latest_version(self));

                // if nonconst min is > const, we can't make this true
                let min = nonconst_range.evaled_range_min(self).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Greater)
                ) {
                    return Ok(true);
                }

                nonconst_var
                    .set_range_max(self, elem.min(nonconst_range.range_max().into_owned()))
                    .into_expr_err(loc)?;
                Ok(false)
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
    ) -> Result<bool, ExprErr> {
        tracing::trace!("Setting range for nonconst from nonconst");
        match op {
            RangeOp::Eq => {
                // check that there is overlap in the ranges
                if !lhs_range.overlaps(&rhs_range, self) {
                    return Ok(true);
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_min(self)
                    .into_expr_err(loc)?
                    .range_ord(&rhs_range.evaled_range_min(self).into_expr_err(loc)?)
                {
                    Some(Ordering::Greater) => {
                        // take lhs range min as its tigher
                        new_rhs
                            .set_range_min(self, Elem::from(new_rhs))
                            .into_expr_err(loc)?;
                    }
                    Some(Ordering::Less) => {
                        // take rhs range min as its tigher
                        new_lhs
                            .set_range_min(self, rhs_range.range_min().into_owned())
                            .into_expr_err(loc)?;
                    }
                    _ => {
                        // equal or not comparable - both keep their minimums
                    }
                }

                // take the tighest range
                match lhs_range
                    .evaled_range_max(self)
                    .into_expr_err(loc)?
                    .range_ord(&rhs_range.evaled_range_max(self).into_expr_err(loc)?)
                {
                    Some(Ordering::Less) => {
                        // take lhs range min as its tigher
                        new_rhs
                            .set_range_max(self, lhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;
                    }
                    Some(Ordering::Greater) => {
                        // take rhs range min as its tigher
                        new_lhs
                            .set_range_max(self, rhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;
                    }
                    _ => {
                        // equal or not comparable - both keep their maximums
                    }
                }

                Ok(false)
            }
            RangeOp::Neq => {
                let rhs_elem = Elem::from(new_rhs.latest_version(self));
                // just add as an exclusion
                lhs_range.add_range_exclusion(rhs_elem);
                new_lhs
                    .set_range_exclusions(self, lhs_range.exclusions)
                    .into_expr_err(loc)?;

                let lhs_elem = Elem::from(new_lhs.latest_version(self));
                // just add as an exclusion
                rhs_range.add_range_exclusion(lhs_elem);
                new_rhs
                    .set_range_exclusions(self, rhs_range.exclusions)
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Gt => {
                let rhs_elem = Elem::from(new_rhs.latest_version(self));
                let lhs_elem = Elem::from(new_lhs.latest_version(self));

                // if lhs.max is <= rhs.min, we can't make this true
                let max = lhs_range.evaled_range_max(self).into_expr_err(loc)?;
                if matches!(
                    max.range_ord(&rhs_elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Less) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                let Some(max_conc) = max.maybe_concrete() else {
                    match lhs_range.max {
                        Elem::Expr(expr) => {
                            let lhs = expr.lhs.maximize(self).into_expr_err(loc)?.to_range_string(true, self).s;
                            let rhs = expr.rhs.maximize(self).into_expr_err(loc)?.to_range_string(true, self).s;
                            // println!("{} != {}", lhs, rhs);
                        }
                        _ => println!("other"),
                    }
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug. Max: {}", max.to_range_string(true, self).s)));
                };

                let one = Concrete::one(&max_conc.val).expect("Cannot decrement range elem by one");

                // we add/sub one to the element because its strict >
                new_lhs
                    .set_range_min(
                        self,
                        (rhs_elem + one.clone().into()).max(lhs_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                new_rhs
                    .set_range_max(
                        self,
                        (lhs_elem - one.into()).min(rhs_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Gte => {
                let rhs_elem = Elem::from(new_rhs.latest_version(self));
                let lhs_elem = Elem::from(new_lhs.latest_version(self));

                // if lhs.max is < rhs.min, we can't make this true
                if matches!(
                    lhs_range
                        .evaled_range_max(self)
                        .into_expr_err(loc)?
                        .range_ord(&rhs_elem.minimize(self).into_expr_err(loc)?),
                    Some(Ordering::Less)
                ) {
                    return Ok(true);
                }

                new_lhs
                    .set_range_min(self, rhs_elem.max(lhs_range.range_min().into_owned()))
                    .into_expr_err(loc)?;
                new_rhs
                    .set_range_max(self, lhs_elem.min(rhs_range.range_max().into_owned()))
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lt => {
                let rhs_elem = Elem::from(new_rhs.latest_version(self));
                let lhs_elem = Elem::from(new_lhs.latest_version(self));

                // if lhs min is >= rhs.max, we can't make this true
                let min = lhs_range.evaled_range_min(self).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&rhs_elem.maximize(self).into_expr_err(loc)?),
                    Some(Ordering::Greater) | Some(Ordering::Equal)
                ) {
                    return Ok(true);
                }

                // we add/sub one to the element because its strict >
                let Some(min_conc) = min.maybe_concrete() else {
                    return Err(ExprErr::BadRange(loc, format!("Expected to have a concrete range by now. This is likely a bug. Min: {}", min.to_range_string(false, self).s)));
                };

                let one = Concrete::one(&min_conc.val).expect("Cannot decrement range elem by one");

                new_lhs
                    .set_range_max(
                        self,
                        (rhs_elem - one.clone().into()).min(lhs_range.range_max().into_owned()),
                    )
                    .into_expr_err(loc)?;
                new_rhs
                    .set_range_min(
                        self,
                        (lhs_elem + one.into()).max(rhs_range.range_min().into_owned()),
                    )
                    .into_expr_err(loc)?;
                Ok(false)
            }
            RangeOp::Lte => {
                let rhs_elem = Elem::from(new_rhs.latest_version(self));
                let lhs_elem = Elem::from(new_lhs.latest_version(self));

                // if nonconst min is > const, we can't make this true
                let min = lhs_range.evaled_range_min(self).into_expr_err(loc)?;
                if matches!(
                    min.range_ord(&rhs_elem.maximize(self).into_expr_err(loc)?),
                    Some(Ordering::Greater)
                ) {
                    return Ok(true);
                }

                new_lhs
                    .set_range_max(self, rhs_elem.min(lhs_range.range_max().into_owned()))
                    .into_expr_err(loc)?;
                new_rhs
                    .set_range_min(self, lhs_elem.max(rhs_range.range_min().into_owned()))
                    .into_expr_err(loc)?;
                Ok(false)
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
        if !tmp_construction.lhs.is_const(self).unwrap() {
            // widen to maximum range :(
            let new_underlying_lhs = self
                .advance_var_in_ctx(tmp_construction.lhs.latest_version(self), loc, ctx)
                .unwrap();
            if let Some(lhs_range) = tmp_construction.lhs.ref_range(self).unwrap() {
                match lhs_range.evaled_range_min(self).unwrap() {
                    Elem::Concrete(c) => {
                        new_underlying_lhs
                            .set_range_min(
                                self,
                                Elem::Concrete(RangeConcrete {
                                    val: Concrete::min(&c.val).unwrap_or_else(|| c.val.clone()),
                                    loc,
                                }),
                            )
                            .unwrap();
                        new_underlying_lhs
                            .set_range_max(
                                self,
                                Elem::Concrete(RangeConcrete {
                                    val: Concrete::max(&c.val).unwrap_or(c.val),
                                    loc,
                                }),
                            )
                            .unwrap();
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
    ) -> Result<(), ExprErr> {
        tracing::trace!("Recursing through range");
        // handle lhs
        let inverse = tmp_construction
            .op
            .inverse()
            .expect("impossible to not invert op");

        if !tmp_construction.lhs.is_const(self).into_expr_err(loc)? {
            tracing::trace!("handling lhs range recursion");
            let adjusted_gt_rhs = ContextVarNode::from({
                let tmp = self.op(
                    loc,
                    rhs_cvar,
                    tmp_construction.rhs.expect("No rhs in tmp_construction"),
                    ctx,
                    inverse,
                    false,
                )?;
                if matches!(tmp, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(tmp, self).into_expr_err(loc)?;
                    return Ok(());
                }
                tmp.expect_single().into_expr_err(loc)?
            });
            let new_underlying_lhs =
                self.advance_var_in_curr_ctx(tmp_construction.lhs.latest_version(self), loc)?;
            if let Some(lhs_range) = new_underlying_lhs
                .underlying(self)
                .into_expr_err(loc)?
                .ty
                .range(self)
                .into_expr_err(loc)?
            {
                if let Some(_rhs_range) = adjusted_gt_rhs
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .ref_range(self)
                    .into_expr_err(loc)?
                {
                    let lhs_range_fn = SolcRange::dyn_fn_from_op(no_flip_op);
                    let new_lhs_range = lhs_range_fn(lhs_range, adjusted_gt_rhs);

                    new_underlying_lhs
                        .set_range_min(self, new_lhs_range.range_min().into_owned())
                        .into_expr_err(loc)?;
                    new_underlying_lhs
                        .set_range_max(self, new_lhs_range.range_max().into_owned())
                        .into_expr_err(loc)?;

                    if new_lhs_range.unsat(self) {
                        *any_unsat = true;
                        ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                        return Ok(());
                    }
                    if let Some(tmp) = new_underlying_lhs.tmp_of(self).into_expr_err(loc)? {
                        self.range_recursion(
                            tmp,
                            (flip_op, no_flip_op),
                            adjusted_gt_rhs,
                            ctx,
                            loc,
                            any_unsat,
                        )?;
                    }
                }
            }
        }

        // handle rhs
        if let Some(rhs) = tmp_construction.rhs {
            if !rhs.is_const(self).into_expr_err(loc)? {
                tracing::trace!("handling rhs range recursion");
                let (needs_inverse, adjusted_gt_rhs) = match tmp_construction.op {
                    RangeOp::Sub(..) => {
                        let concrete = ConcreteNode(
                            self.add_node(Node::Concrete(Concrete::Int(256, I256::from(-1i32))))
                                .index(),
                        );
                        let lhs_cvar = ContextVar::new_from_concrete(loc, ctx, concrete, self)
                            .into_expr_err(loc)?;
                        let tmp_lhs =
                            ContextVarNode::from(self.add_node(Node::ContextVar(lhs_cvar)));

                        // tmp_rhs = rhs_cvar * -1
                        let tmp_rhs =
                            self.op(loc, rhs_cvar, tmp_lhs, ctx, RangeOp::Mul(false), false)?;
                        if matches!(tmp_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(tmp_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let tmp_rhs =
                            ContextVarNode::from(tmp_rhs.expect_single().into_expr_err(loc)?);

                        // new_rhs = (rhs_cvar * -1) + tmp_construction.lhs
                        let new_rhs =
                            self.op(loc, tmp_rhs, tmp_construction.lhs, ctx, inverse, false)?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (true, new_rhs)
                    }
                    RangeOp::Add(..) => {
                        let new_rhs =
                            self.op(loc, rhs_cvar, tmp_construction.lhs, ctx, inverse, false)?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Mul(..) => {
                        let new_rhs =
                            self.op(loc, rhs_cvar, tmp_construction.lhs, ctx, inverse, false)?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        // panic!("HERE: old: {:#?},\nnew: {:#?}", rhs_cvar.underlying(self), new_rhs.underlying(self));
                        (false, new_rhs)
                    }
                    RangeOp::Div(..) => {
                        let new_rhs =
                            self.op(loc, rhs_cvar, tmp_construction.lhs, ctx, inverse, false)?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        // panic!("HERE: old: {:#?},\nnew: {:#?}", rhs_cvar.underlying(self), new_rhs.underlying(self));
                        (false, new_rhs)
                    }
                    e => panic!("here {e:?}"),
                };

                let new_underlying_rhs =
                    self.advance_var_in_curr_ctx(rhs.latest_version(self), loc)?;
                if let Some(lhs_range) = new_underlying_rhs
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .range(self)
                    .into_expr_err(loc)?
                {
                    if let Some(_rhs_range) = adjusted_gt_rhs
                        .underlying(self)
                        .into_expr_err(loc)?
                        .ty
                        .ref_range(self)
                        .into_expr_err(loc)?
                    {
                        let new_lhs_range = if needs_inverse {
                            let lhs_range_fn = SolcRange::dyn_fn_from_op(flip_op);
                            lhs_range_fn(lhs_range, adjusted_gt_rhs)
                        } else {
                            let lhs_range_fn = SolcRange::dyn_fn_from_op(no_flip_op);
                            lhs_range_fn(lhs_range, adjusted_gt_rhs)
                        };

                        new_underlying_rhs
                            .set_range_min(self, new_lhs_range.range_min().into_owned())
                            .into_expr_err(loc)?;
                        new_underlying_rhs
                            .set_range_max(self, new_lhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;

                        if new_lhs_range.unsat(self) {
                            *any_unsat = true;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(());
                        }

                        if let Some(tmp) = new_underlying_rhs.tmp_of(self).into_expr_err(loc)? {
                            self.range_recursion(
                                tmp,
                                (flip_op, no_flip_op),
                                adjusted_gt_rhs,
                                ctx,
                                loc,
                                any_unsat,
                            )?;
                        }
                    }
                }
            }
        }

        Ok(())
    }
}
