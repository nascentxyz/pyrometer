use crate::{require::Require, yul::YulBuilder, ContextBuilder};

use graph::{
    elem::*,
    nodes::{
        Concrete, ConcreteNode, Context, ContextNode, ContextVar, ContextVarNode, ExprRet,
        SubContextKind,
    },
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use ethers_core::types::U256;
use solang_parser::pt::{
    CodeLocation, Expression, Identifier, Loc, YulBlock, YulExpression, YulFunctionCall,
    YulStatement, YulSwitchOptions,
};

impl<T> YulCondOp for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized
{
}

/// Trait for dealing with conditional operations in yul
pub trait YulCondOp:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized
{
    #[tracing::instrument(level = "trace", skip_all)]
    /// Handle a yul conditional operation statement
    fn yul_cond_op_stmt(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        if_expr: &YulExpression,
        true_stmt: &YulBlock,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let true_subctx_kind = SubContextKind::new_fork(ctx, true);
            let tctx =
                Context::new_subctx(true_subctx_kind, loc, analyzer, None).into_expr_err(loc)?;
            let true_subctx = ContextNode::from(analyzer.add_node(Node::Context(tctx)));
            let false_subctx_kind = SubContextKind::new_fork(ctx, false);
            let fctx =
                Context::new_subctx(false_subctx_kind, loc, analyzer, None).into_expr_err(loc)?;
            let false_subctx = ContextNode::from(analyzer.add_node(Node::Context(fctx)));
            ctx.set_child_fork(true_subctx, false_subctx, analyzer)
                .into_expr_err(loc)?;
            let ctx_fork = analyzer.add_node(Node::ContextFork);
            analyzer.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::ContextFork));
            analyzer.add_edge(
                NodeIdx::from(true_subctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );
            analyzer.add_edge(
                NodeIdx::from(false_subctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );

            analyzer.parse_ctx_yul_expr(arena, if_expr, true_subctx)?;
            analyzer.apply_to_edges(true_subctx, loc, arena, &|analyzer, arena, ctx, loc| {
                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(
                        loc,
                        "True conditional had no lhs".to_string(),
                    ));
                };

                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }

                analyzer.match_yul_true(arena, ctx, if_expr.loc(), &ret)
            })?;

            analyzer.parse_ctx_yul_statement(
                arena,
                &YulStatement::Block(true_stmt.clone()),
                true_subctx,
            );
            // let false_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
            //     loc,
            //     id: Identifier {
            //         loc,
            //         name: "iszero".to_string(),
            //     },
            //     arguments: vec![if_expr.clone()],
            // }));
            analyzer.parse_ctx_yul_expr(arena, if_expr, false_subctx)?;
            analyzer.apply_to_edges(false_subctx, loc, arena, &|analyzer, arena, ctx, loc| {
                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(
                        loc,
                        "False conditional had no lhs".to_string(),
                    ));
                };

                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }

                analyzer.match_yul_false(arena, ctx, if_expr.loc(), &ret)
            })
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Handle a yul if-else
    fn yul_if_else(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        if_else_chain: &IfElseChain,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let true_subctx_kind = SubContextKind::new_fork(ctx, true);
            let tctx =
                Context::new_subctx(true_subctx_kind, loc, analyzer, None).into_expr_err(loc)?;
            let true_subctx = ContextNode::from(analyzer.add_node(Node::Context(tctx)));
            let false_subctx_kind = SubContextKind::new_fork(ctx, false);
            let fctx =
                Context::new_subctx(false_subctx_kind, loc, analyzer, None).into_expr_err(loc)?;
            let false_subctx = ContextNode::from(analyzer.add_node(Node::Context(fctx)));
            ctx.set_child_fork(true_subctx, false_subctx, analyzer)
                .into_expr_err(loc)?;
            let ctx_fork = analyzer.add_node(Node::ContextFork);
            analyzer.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::ContextFork));
            analyzer.add_edge(
                NodeIdx::from(true_subctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );
            analyzer.add_edge(
                NodeIdx::from(false_subctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );

            let if_expr_loc = if_else_chain.if_expr.loc();
            analyzer.apply_to_edges(
                true_subctx,
                if_expr_loc,
                arena,
                &|analyzer, arena, ctx, loc| {
                    analyzer.parse_ctx_yul_expr(arena, &if_else_chain.if_expr, true_subctx)?;
                    analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, _loc| {
                        let Some(true_vars) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoRhs(
                                loc,
                                "Yul switch statement was missing a case discriminator".to_string(),
                            ));
                        };

                        if matches!(true_vars, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(true_vars, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.match_yul_true(arena, ctx, loc, &true_vars)?;
                        analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, _loc| {
                            analyzer.parse_ctx_yul_statement(arena, &if_else_chain.true_stmt, ctx);
                            Ok(())
                        })
                    })
                },
            )?;

            if let Some(next) = &if_else_chain.next {
                match next {
                    ElseOrDefault::Default(default) => analyzer.apply_to_edges(
                        false_subctx,
                        loc,
                        arena,
                        &|analyzer, arena, ctx, _loc| {
                            analyzer.parse_ctx_yul_statement(arena, default, ctx);
                            Ok(())
                        },
                    ),
                    ElseOrDefault::Else(iec) => analyzer.apply_to_edges(
                        false_subctx,
                        loc,
                        arena,
                        &|analyzer, arena, ctx, loc| analyzer.yul_if_else(arena, loc, iec, ctx),
                    ),
                }
            } else {
                Ok(())
            }
        })
    }

    /// Helper for the `true` evaluation of a yul conditional
    fn match_yul_true(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        true_cvars: &ExprRet,
    ) -> Result<(), ExprErr> {
        match true_cvars {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc)?,
            ExprRet::Single(_true_cvar) | ExprRet::SingleLiteral(_true_cvar) => {
                let cnode = ConcreteNode::from(self.add_node(Concrete::Uint(1, U256::from(0))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                        .into_expr_err(loc)?,
                );
                let rhs_paths =
                    ExprRet::Single(ContextVarNode::from(self.add_node(tmp_true)).into());

                self.handle_require_inner(arena, ctx, true_cvars, &rhs_paths, RangeOp::Gt, loc)?;
            }
            ExprRet::Multi(ref true_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                true_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_true(arena, ctx, loc, expr_ret))?;
            }
            ExprRet::Null => {}
        }
        Ok(())
    }

    /// Helper for the `false` evaluation of a yul conditional
    fn match_yul_false(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        false_cvars: &ExprRet,
    ) -> Result<(), ExprErr> {
        match false_cvars {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc)?,
            ExprRet::Single(_false_cvar) | ExprRet::SingleLiteral(_false_cvar) => {
                let cnode = ConcreteNode::from(self.add_node(Concrete::Uint(1, U256::from(0))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                        .into_expr_err(loc)?,
                );
                let rhs_paths =
                    ExprRet::Single(ContextVarNode::from(self.add_node(tmp_true)).into());

                self.handle_require_inner(arena, ctx, false_cvars, &rhs_paths, RangeOp::Eq, loc)?;
            }
            ExprRet::Multi(ref false_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                false_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_false(arena, ctx, loc, expr_ret))?;
            }
            ExprRet::Null => {}
        }

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Handle a yul swithc statement by converting it into an if-else chain
    fn yul_switch_stmt(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        condition: YulExpression,
        cases: Vec<YulSwitchOptions>,
        default: Option<YulSwitchOptions>,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let iec = IfElseChain::from(loc, (condition, cases, default))?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, _loc| {
            analyzer.yul_if_else(arena, loc, &iec, ctx)
        })
    }
}

#[derive(Clone, Debug)]
/// A yul-based if-else chain, which represents a switch statement
pub struct IfElseChain {
    pub if_expr: YulExpression,
    pub true_stmt: YulStatement,
    pub next: Option<ElseOrDefault>,
}

#[derive(Clone, Debug)]
/// Wrapper over a switch statement that denotes either another else statement or the default case
pub enum ElseOrDefault {
    Else(Box<IfElseChain>),
    Default(YulStatement),
}

impl From<IfElseChain> for ElseOrDefault {
    fn from(iec: IfElseChain) -> Self {
        Self::Else(Box::new(iec))
    }
}

impl IfElseChain {
    pub fn from_child(ed: ElseOrDefault) -> Option<Self> {
        match ed {
            ElseOrDefault::Else(iec) => Some(*iec),
            _ => None,
        }
    }
}

impl From<YulSwitchOptions> for ElseOrDefault {
    fn from(default: YulSwitchOptions) -> Self {
        match default {
            YulSwitchOptions::Default(_loc, block) => {
                ElseOrDefault::Default(YulStatement::Block(block))
            }
            _ => unreachable!("case as default"),
        }
    }
}

pub type SwitchInfo = (
    YulExpression,
    Vec<YulSwitchOptions>,
    Option<YulSwitchOptions>,
);

impl IfElseChain {
    pub fn from(loc: Loc, (condition, cases, default): SwitchInfo) -> Result<Self, ExprErr> {
        let mut child: Option<ElseOrDefault> = default.map(|default| default.into());

        cases.into_iter().rev().for_each(|case| {
            let mut chain_part: IfElseChain = From::from((condition.clone(), case));
            if let Some(c) = child.take() {
                chain_part.next = c.into();
            }
            child = Some(chain_part.into());
        });
        let Some(child) = child else {
            return Err(ExprErr::NoRhs(
                loc,
                "No cases or default found for switch statement".to_string(),
            ));
        };

        let Some(iec) = IfElseChain::from_child(child) else {
            return Err(ExprErr::NoRhs(
                loc,
                "No cases or default found for switch statement".to_string(),
            ));
        };
        Ok(iec)
    }
}

impl From<(YulExpression, YulSwitchOptions)> for IfElseChain {
    fn from((condition, case): (YulExpression, YulSwitchOptions)) -> Self {
        match case {
            YulSwitchOptions::Case(loc, expr, stmt) => {
                let if_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
                    loc,
                    id: Identifier {
                        loc,
                        name: "eq".to_string(),
                    },
                    arguments: vec![condition, expr],
                }));
                IfElseChain {
                    if_expr,
                    true_stmt: YulStatement::Block(stmt),
                    next: None,
                }
            }
            YulSwitchOptions::Default(_loc, _block) => {
                unreachable!("We shouldn't have a `default` case in cases - only in the `default` input parameter")
            }
        }
    }
}
