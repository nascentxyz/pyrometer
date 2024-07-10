use crate::{BinOp, ContextBuilder, ExpressionParser, Variable};

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

use ethers_core::types::I256;
use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Loc},
};

use std::cmp::Ordering;

impl<T> Require for T where T: Variable + BinOp + Sized + AnalyzerBackend {}

/// Deals with require and assert statements, as well as adjusts bounds for variables
pub trait Require: AnalyzerBackend + Variable + BinOp + Sized {
    /// Inverts a comparator expression
    fn inverse_expr(&self, expr: Expression) -> Expression {
        match expr {
            Expression::Equal(loc, lhs, rhs) => Expression::NotEqual(loc, lhs, rhs),
            Expression::NotEqual(loc, lhs, rhs) => Expression::Equal(loc, lhs, rhs),
            Expression::Less(loc, lhs, rhs) => Expression::MoreEqual(loc, lhs, rhs),
            Expression::More(loc, lhs, rhs) => Expression::LessEqual(loc, lhs, rhs),
            Expression::MoreEqual(loc, lhs, rhs) => Expression::Less(loc, lhs, rhs),
            Expression::LessEqual(loc, lhs, rhs) => Expression::More(loc, lhs, rhs),
            // Expression::And(loc, lhs, rhs) => {
            //     Expression::Or(loc, Box::new(self.inverse_expr(*lhs)), Box::new(self.inverse_expr(*rhs)))
            // }
            // Expression::Or(loc, lhs, rhs) => {
            //     Expression::And(loc, Box::new(self.inverse_expr(*lhs)), Box::new(self.inverse_expr(*rhs)))
            // }
            // Expression::Not(loc, lhs) => {
            //     Expression::Equal(loc, lhs, Box::new(Expression::BoolLiteral(loc, true)))
            // }
            e => Expression::Not(e.loc(), Box::new(e)),
        }
    }

    /// Handles a require expression
    #[tracing::instrument(level = "trace", skip_all)]
    fn handle_require(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        inputs: &[Expression],
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        ctx.add_gas_cost(self, shared::gas::BIN_OP_GAS)
            .into_expr_err(inputs[0].loc())?;
        match inputs.first().expect("No lhs input for require statement") {
            Expression::Equal(loc, lhs, rhs) => {
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `==` had no right hand side".to_string(),
                        ));
                    };

                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `==` had no left hand side".to_string(),
                            ));
                        };

                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Eq,
                            RangeOp::Eq,
                            (RangeOp::Neq, RangeOp::Eq),
                        )
                    })
                })
            }
            Expression::NotEqual(loc, lhs, rhs) => {
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `!=` had no right hand side".to_string(),
                        ));
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `!=` had no left hand side".to_string(),
                            ));
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
                            ctx,
                            loc,
                            &lhs_paths.flatten(),
                            &rhs_paths,
                            RangeOp::Neq,
                            RangeOp::Neq,
                            (RangeOp::Eq, RangeOp::Neq),
                        )
                    })
                })
            }
            Expression::Less(loc, lhs, rhs) => {
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `<` had no right hand side".to_string(),
                        ));
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `<` had no left hand side".to_string(),
                            ));
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
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
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `>` had no right hand side".to_string(),
                        ));
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `>` had no left hand side".to_string(),
                            ));
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
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
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `>=` had no right hand side".to_string(),
                        ));
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `>=` had no left hand side".to_string(),
                            ));
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
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
                self.parse_ctx_expr(arena, rhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Require operation `<=` had no right hand side".to_string(),
                        ));
                    };
                    let rhs_paths = rhs_paths.flatten();

                    if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, lhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(lhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `<=` had no left hand side".to_string(),
                            ));
                        };
                        if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.handle_require_inner(
                            arena,
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
                self.parse_ctx_expr(arena, lhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Require operation `NOT` had no left hand side".to_string(),
                        ));
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let cnode = ConcreteNode::from(
                        analyzer.add_node(Node::Concrete(Concrete::Bool(false))),
                    );
                    let tmp_false = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(loc)?,
                    );
                    let rhs_paths =
                        ExprRet::Single(ContextVarNode::from(analyzer.add_node(tmp_false)).into());
                    analyzer.handle_require_inner(
                        arena,
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Eq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
            Expression::And(loc, lhs, rhs) => {
                self.parse_ctx_expr(arena, lhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Require operation `&&` had no left hand side".to_string(),
                        ));
                    };

                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, rhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(rhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `&&` had no left hand side".to_string(),
                            ));
                        };

                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        let cnode = ConcreteNode::from(
                            analyzer.add_node(Node::Concrete(Concrete::Bool(true))),
                        );
                        let tmp_true = Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                                .into_expr_err(loc)?,
                        );
                        let node = analyzer.add_node(tmp_true);
                        ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        let tmp_rhs_paths = ExprRet::Single(node);

                        // NOTE: the following is *sequence dependent*
                        // we want to update the parts *before* the `And` op
                        // to ensure the ctx_dep is correct

                        // update the part's bounds
                        let lhs_cvar =
                            ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                        let underlying = lhs_cvar.underlying(analyzer).into_expr_err(loc)?;
                        if let Some(tmp) = underlying.tmp_of {
                            if let Some((op, _inv_op, pair)) = tmp.op.require_parts() {
                                analyzer.handle_require_inner(
                                    arena,
                                    ctx,
                                    loc,
                                    &ExprRet::Single(tmp.lhs.into()),
                                    &ExprRet::Single(tmp.rhs.unwrap().into()),
                                    op,
                                    op,
                                    pair,
                                )?;
                            }
                        }

                        // update the part's bounds
                        let rhs_cvar =
                            ContextVarNode::from(rhs_paths.expect_single().into_expr_err(loc)?);
                        let underlying = rhs_cvar.underlying(analyzer).into_expr_err(loc)?;
                        if let Some(tmp) = underlying.tmp_of {
                            if let Some((op, _inv_op, pair)) = tmp.op.require_parts() {
                                analyzer.handle_require_inner(
                                    arena,
                                    ctx,
                                    loc,
                                    &ExprRet::Single(tmp.lhs.into()),
                                    &ExprRet::Single(tmp.rhs.unwrap().into()),
                                    op,
                                    op,
                                    pair,
                                )?;
                            }
                        }

                        analyzer.handle_require_inner(
                            arena,
                            ctx,
                            loc,
                            &lhs_paths,
                            &tmp_rhs_paths,
                            RangeOp::Eq,
                            RangeOp::Eq,
                            (RangeOp::Neq, RangeOp::Eq),
                        )?;

                        analyzer.handle_require_inner(
                            arena,
                            ctx,
                            loc,
                            &rhs_paths,
                            &tmp_rhs_paths,
                            RangeOp::Eq,
                            RangeOp::Eq,
                            (RangeOp::Neq, RangeOp::Eq),
                        )?;

                        Ok(())
                    })
                })
            }
            Expression::Or(loc, lhs, rhs) => {
                self.parse_ctx_expr(arena, lhs, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Require operation `||` had no left hand side".to_string(),
                        ));
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_expr(arena, rhs, ctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(rhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "Require operation `||` had no left hand side".to_string(),
                            ));
                        };

                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        let lhs_cvar =
                            ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                        let rhs_cvar =
                            ContextVarNode::from(rhs_paths.expect_single().into_expr_err(loc)?);

                        let elem = Elem::Expr(RangeExpr::new(
                            lhs_cvar.into(),
                            RangeOp::Or,
                            rhs_cvar.into(),
                        ));
                        let range = SolcRange::new(elem.clone(), elem, vec![]);

                        let new_lhs_underlying = ContextVar {
                            loc: Some(loc),
                            name: format!(
                                "tmp{}({} {} {})",
                                ctx.new_tmp(analyzer).into_expr_err(loc)?,
                                lhs_cvar.name(analyzer).into_expr_err(loc)?,
                                RangeOp::Or.to_string(),
                                rhs_cvar.name(analyzer).into_expr_err(loc)?
                            ),
                            display_name: format!(
                                "({} {} {})",
                                lhs_cvar.display_name(analyzer).into_expr_err(loc)?,
                                RangeOp::Or.to_string(),
                                rhs_cvar.display_name(analyzer).into_expr_err(loc)?
                            ),
                            storage: None,
                            is_tmp: true,
                            is_symbolic: lhs_cvar.is_symbolic(analyzer).into_expr_err(loc)?
                                || rhs_cvar.is_symbolic(analyzer).into_expr_err(loc)?,
                            is_return: false,
                            tmp_of: Some(TmpConstruction::new(
                                lhs_cvar,
                                RangeOp::Or,
                                Some(rhs_cvar),
                            )),
                            dep_on: {
                                let mut deps =
                                    lhs_cvar.dependent_on(analyzer, true).into_expr_err(loc)?;
                                deps.extend(
                                    rhs_cvar.dependent_on(analyzer, true).into_expr_err(loc)?,
                                );
                                Some(deps)
                            },
                            ty: VarType::BuiltIn(
                                analyzer.builtin_or_add(Builtin::Bool).into(),
                                Some(range),
                            ),
                        };
                        let or_var = ContextVarNode::from(
                            analyzer.add_node(Node::ContextVar(new_lhs_underlying)),
                        );
                        let cnode = ConcreteNode::from(
                            analyzer.add_node(Node::Concrete(Concrete::Bool(true))),
                        );
                        let tmp_true = Node::ContextVar(
                            ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                                .into_expr_err(loc)?,
                        );
                        let node = analyzer.add_node(tmp_true);
                        ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        let rhs_paths = ExprRet::Single(node);
                        analyzer.handle_require_inner(
                            arena,
                            ctx,
                            loc,
                            &ExprRet::Single(or_var.into()),
                            &rhs_paths,
                            RangeOp::Eq,
                            RangeOp::Eq,
                            (RangeOp::Neq, RangeOp::Eq),
                        )
                    })
                })
            }
            other => {
                self.parse_ctx_expr(arena, other, ctx)?;
                self.apply_to_edges(ctx, other.loc(), arena, &|analyzer, arena, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Require operation had no left hand side".to_string(),
                        ));
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    let tmp_true = analyzer.add_concrete_var(ctx, Concrete::Bool(true), loc)?;
                    let rhs_paths = ExprRet::Single(tmp_true.0.into());
                    analyzer.handle_require_inner(
                        arena,
                        ctx,
                        loc,
                        &lhs_paths,
                        &rhs_paths,
                        RangeOp::Eq,
                        RangeOp::Eq,
                        (RangeOp::Neq, RangeOp::Eq),
                    )
                })
            }
        }
    }

    /// Do matching on [`ExprRet`]s to actually perform the require statement evaluation
    fn handle_require_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
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
                    .cast_from(&ContextVarNode::from(*rhs), self, arena)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    arena,
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
                    .cast_from(&ContextVarNode::from(*lhs), self, arena)
                    .into_expr_err(loc)?;
                self.handle_require_inner(
                    arena,
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
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let new_lhs = self.advance_var_in_ctx(lhs_cvar, loc, ctx)?;
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                let new_rhs = self.advance_var_in_ctx(rhs_cvar, loc, ctx)?;

                self.require(arena, new_lhs, new_rhs, ctx, loc, op, rhs_op, recursion_ops)?;
                Ok(())
            }
            (l @ ExprRet::Single(_) | l @ ExprRet::SingleLiteral(_), ExprRet::Multi(rhs_sides)) => {
                rhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(
                        arena,
                        ctx,
                        loc,
                        l,
                        expr_ret,
                        op,
                        rhs_op,
                        recursion_ops,
                    )
                })
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                lhs_sides.iter().try_for_each(|expr_ret| {
                    self.handle_require_inner(
                        arena,
                        ctx,
                        loc,
                        expr_ret,
                        r,
                        op,
                        rhs_op,
                        recursion_ops,
                    )
                })
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.handle_require_inner(
                                arena,
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
                            arena,
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
        arena: &mut RangeArena<Elem<Concrete>>,
        mut new_lhs: ContextVarNode,
        mut new_rhs: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        op: RangeOp,
        rhs_op: RangeOp,
        _recursion_ops: (RangeOp, RangeOp),
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
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, true) => {
                        if self.update_nonconst_from_const(
                            arena, ctx, loc, op, new_rhs, new_lhs, lhs_range,
                        )? {
                            tracing::trace!("half-const killable");
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(None);
                        }
                    }
                    (false, false) => {
                        if self.update_nonconst_from_nonconst(
                            arena, ctx, loc, op, new_lhs, new_rhs, lhs_range, rhs_range,
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
            tracing::trace!("done range updating");
            new_rhs = new_rhs.latest_version_or_inherited_in_ctx(ctx, self);
            new_lhs = new_lhs.latest_version_or_inherited_in_ctx(ctx, self);

            let rhs_display_name = new_rhs.display_name(self).into_expr_err(loc)?;
            let display_name = if rhs_display_name == "true" {
                (new_lhs.display_name(self).into_expr_err(loc)?).to_string()
            } else {
                format!(
                    "({} {} {rhs_display_name})",
                    new_lhs.display_name(self).into_expr_err(loc)?,
                    op.to_string(),
                )
            };

            // we take the previous version because for the solver we actually dont want the updated range
            let base = Elem::Expr(RangeExpr::new(
                new_lhs.previous_version(self).unwrap_or(new_lhs).into(),
                op,
                new_rhs.previous_version(self).unwrap_or(new_rhs).into(),
            ));

            // construct a temporary variable that represent the conditional we just checked
            let conditional_var = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self).into_expr_err(loc)?,
                    new_lhs.name(self).into_expr_err(loc)?,
                    op.to_string(),
                    new_rhs.name(self).into_expr_err(loc)?,
                ),
                display_name: display_name.clone(),
                storage: None,
                is_tmp: true,
                tmp_of: Some(TmpConstruction::new(new_lhs, op, Some(new_rhs))),
                dep_on: {
                    let mut deps = new_lhs.dependent_on(self, true).into_expr_err(loc)?;
                    deps.extend(new_rhs.dependent_on(self, true).into_expr_err(loc)?);
                    Some(deps)
                },
                is_symbolic: new_lhs.is_symbolic(self).into_expr_err(loc)?
                    || new_rhs.is_symbolic(self).into_expr_err(loc)?,
                is_return: false,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                    // we set the minimum to `true` so that if `elem` evaluates to false,
                    // we can discover the unsatisifiability
                    Some(SolcRange::new(base.clone(), base, vec![])),
                ),
            };

            let conditional_cvar =
                ContextVarNode::from(self.add_node(Node::ContextVar(conditional_var)));
            ctx.add_var(conditional_cvar, self).into_expr_err(loc)?;
            self.add_edge(conditional_cvar, ctx, Edge::Context(ContextEdge::Variable));

            let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
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
                    op.to_string(),
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

            let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(tmp_var)));
            ctx.add_var(cvar, self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

            tmp_cvar = Some(cvar);

            tracing::trace!("checking unsat");
            any_unsat |= new_var_range.unsat(self, arena);

            ctx.add_ctx_dep(conditional_cvar, self, arena)
                .into_expr_err(loc)?;

            if any_unsat || ctx.unreachable(self, arena).into_expr_err(loc)? {
                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                return Ok(None);
            }
        }

        tracing::trace!(
            "{} is tmp: {}",
            new_lhs.display_name(self).unwrap(),
            new_lhs.is_tmp(self).unwrap()
        );
        // if let Some(tmp) = new_lhs.tmp_of(self).into_expr_err(loc)? {
        //     if tmp.op.inverse().is_some() && !matches!(op, RangeOp::Eq | RangeOp::Neq) {
        //         // self.range_recursion(tmp, recursion_ops, new_rhs, ctx, loc, &mut any_unsat)?;
        //     } else {
        //         match tmp.op {
        //             RangeOp::Not => {}
        //             _ => {
        //                 self.uninvertable_range_recursion(arena, tmp, new_lhs, new_rhs, loc, ctx);
        //             }
        //         }
        //     }
        // }

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
        match op {
            RangeOp::Eq => {
                // check that the constant is contained in the nonconst var range
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));
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
                let elem = Elem::from(const_var.latest_version_or_inherited_in_ctx(ctx, self));

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
                    let idx = arena.idx_or_upsert(elem, self);
                    nonconst_range.add_range_exclusion(idx);
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
                        op.to_string(),
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

                let rhs_elem = Elem::from(new_rhs.latest_version_or_inherited_in_ctx(ctx, self));
                // just add as an exclusion
                let idx = arena.idx_or_upsert(rhs_elem, self);
                lhs_range.add_range_exclusion(idx);
                new_lhs
                    .set_range_exclusions(self, lhs_range.exclusions)
                    .into_expr_err(loc)?;

                let lhs_elem = Elem::from(new_lhs.latest_version_or_inherited_in_ctx(ctx, self));
                // just add as an exclusion
                let idx = arena.idx_or_upsert(lhs_elem, self);
                rhs_range.add_range_exclusion(idx);
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

                let new_new_lhs = self.advance_var_in_curr_ctx(new_lhs, loc)?;
                let new_new_rhs = self.advance_var_in_curr_ctx(new_rhs, loc)?;

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

                let new_new_lhs = self.advance_var_in_curr_ctx(new_lhs, loc)?;
                let new_new_rhs = self.advance_var_in_curr_ctx(new_rhs, loc)?;

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

    /// Recursively updates the range for a
    fn range_recursion(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        tmp_construction: TmpConstruction,
        (flip_op, no_flip_op): (RangeOp, RangeOp),
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        loc: Loc,
        any_unsat: &mut bool,
    ) -> Result<(), ExprErr> {
        tracing::trace!("Recursing through range");
        // handle lhs
        let Some(inverse) = tmp_construction.op.inverse() else {
            return Ok(());
        };

        if !tmp_construction
            .lhs
            .is_const(self, arena)
            .into_expr_err(loc)?
        {
            tracing::trace!("handling lhs range recursion");
            let adjusted_gt_rhs = ContextVarNode::from({
                let tmp = self.op(
                    arena,
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
            let new_underlying_lhs = self.advance_var_in_curr_ctx(
                tmp_construction
                    .lhs
                    .latest_version_or_inherited_in_ctx(ctx, self),
                loc,
            )?;
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
                        .set_range_min(self, arena, new_lhs_range.range_min().into_owned())
                        .into_expr_err(loc)?;
                    new_underlying_lhs
                        .set_range_max(self, arena, new_lhs_range.range_max().into_owned())
                        .into_expr_err(loc)?;

                    if new_lhs_range.unsat(self, arena) {
                        *any_unsat = true;
                        ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                        return Ok(());
                    }
                    if let Some(tmp) = new_underlying_lhs.tmp_of(self).into_expr_err(loc)? {
                        self.range_recursion(
                            arena,
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
            if !rhs.is_const(self, arena).into_expr_err(loc)? {
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
                        let tmp_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_lhs,
                            ctx,
                            RangeOp::Mul(false),
                            false,
                        )?;
                        if matches!(tmp_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(tmp_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let tmp_rhs =
                            ContextVarNode::from(tmp_rhs.expect_single().into_expr_err(loc)?);

                        // new_rhs = (rhs_cvar * -1) + tmp_construction.lhs
                        let new_rhs = self.op(
                            arena,
                            loc,
                            tmp_rhs,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (true, new_rhs)
                    }
                    RangeOp::Add(..) => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Mul(..) => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Div(..) => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Shl => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Shr => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Eq => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    RangeOp::Neq => {
                        let new_rhs = self.op(
                            arena,
                            loc,
                            rhs_cvar,
                            tmp_construction.lhs,
                            ctx,
                            inverse,
                            false,
                        )?;
                        if matches!(new_rhs, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(new_rhs, self).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let new_rhs =
                            ContextVarNode::from(new_rhs.expect_single().into_expr_err(loc)?);
                        (false, new_rhs)
                    }
                    e => panic!("here {e:?}"),
                };

                let new_underlying_rhs = self.advance_var_in_curr_ctx(
                    rhs.latest_version_or_inherited_in_ctx(ctx, self),
                    loc,
                )?;
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
                            .set_range_min(self, arena, new_lhs_range.range_min().into_owned())
                            .into_expr_err(loc)?;
                        new_underlying_rhs
                            .set_range_max(self, arena, new_lhs_range.range_max().into_owned())
                            .into_expr_err(loc)?;

                        if new_lhs_range.unsat(self, arena) {
                            *any_unsat = true;
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            return Ok(());
                        }

                        if let Some(tmp) = new_underlying_rhs.tmp_of(self).into_expr_err(loc)? {
                            self.range_recursion(
                                arena,
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
