use crate::context::exprs::IntoExprErr;
use crate::context::yul::YulBuilder;
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use crate::Concrete;
use crate::ConcreteNode;
use crate::{exprs::Require, AnalyzerLike};
use shared::context::ExprRet;
use shared::range::elem::RangeOp;
use shared::{context::*, Edge, Node, NodeIdx};
use solang_parser::pt::Identifier;
use solang_parser::pt::YulBlock;
use solang_parser::pt::YulFunctionCall;
use solang_parser::pt::YulSwitchOptions;

use solang_parser::pt::CodeLocation;
use solang_parser::pt::{Expression, Loc};
use solang_parser::pt::{YulExpression, YulStatement};

impl<T> YulCondOp for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized
{}
pub trait YulCondOp: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn yul_cond_op_stmt(
        &mut self,
        loc: Loc,
        if_expr: &YulExpression,
        true_stmt: &YulBlock,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let true_subctx = ContextNode::from(
                analyzer.add_node(Node::Context(
                    Context::new_subctx(ctx, None, loc, Some("true"), None, false, analyzer, None)
                        .into_expr_err(loc)?,
                )),
            );
            let false_subctx = ContextNode::from(
                analyzer.add_node(Node::Context(
                    Context::new_subctx(ctx, None, loc, Some("false"), None, false, analyzer, None)
                        .into_expr_err(loc)?,
                )),
            );
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

            analyzer.parse_ctx_yul_expr(if_expr, true_subctx)?;
            analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "True conditional had no lhs".to_string()));
                };

                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }

                analyzer.match_yul_true(ctx, if_expr.loc(), &ret)
            })?;

            analyzer.parse_ctx_yul_statement(&YulStatement::Block(true_stmt.clone()), true_subctx);
            let false_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
                loc,
                id: Identifier {
                    loc,
                    name: "iszero".to_string(),
                },
                arguments: vec![if_expr.clone()],
            }));
            analyzer.parse_ctx_yul_expr(&false_expr, false_subctx)?;
            analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "True conditional had no lhs".to_string()));
                };

                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }

                analyzer.match_yul_false(ctx, if_expr.loc(), &ret)
            })
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn yul_if_else(
        &mut self,
        loc: Loc,
        if_else_chain: &IfElseChain,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let true_subctx = ContextNode::from(
                analyzer.add_node(Node::Context(
                    Context::new_subctx(ctx, None, loc, Some("true"), None, false, analyzer, None)
                        .into_expr_err(loc)?,
                )),
            );
            let false_subctx = ContextNode::from(
                analyzer.add_node(Node::Context(
                    Context::new_subctx(ctx, None, loc, Some("false"), None, false, analyzer, None)
                        .into_expr_err(loc)?,
                )),
            );
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


            println!("yul if else: {:?}", if_else_chain.if_expr);
            let if_expr_loc = if_else_chain.if_expr.loc();
            analyzer.apply_to_edges(true_subctx, if_expr_loc, &|analyzer, ctx, loc| {
                analyzer.parse_ctx_yul_expr(&if_else_chain.if_expr, true_subctx)?;
                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                    let Some(true_vars) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul switch statement was missing a case discriminator".to_string()))
                    };

                    if matches!(true_vars, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(true_vars, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_yul_true(ctx, loc, &true_vars)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                        println!("\n\nyul true stmt: {:?}\n\n", if_else_chain.true_stmt);
                        analyzer.parse_ctx_yul_statement(&if_else_chain.true_stmt, ctx);
                        Ok(())
                    })
                })
            })?;


            if let Some(next) = &if_else_chain.next {
                match next {
                    ElseOrDefault::Default(default) => {
                        println!("handling default: {default:?}");
                        analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, _loc| {
                            analyzer.parse_ctx_yul_statement(default, ctx);
                            Ok(())
                        })
                    }
                    ElseOrDefault::Else(iec) => {
                        analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, loc| {
                            analyzer.yul_if_else(loc, iec, ctx)
                        })
                    }
                }
            } else {
                Ok(())
            }
        })
    }

    fn match_yul_true(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        true_cvars: &ExprRet,
    ) -> Result<(), ExprErr> {
        match true_cvars {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc)?,
            ExprRet::Single(_true_cvar) | ExprRet::SingleLiteral(_true_cvar) => {
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                        .into_expr_err(loc)?,
                );
                let rhs_paths =
                    ExprRet::Single(ContextVarNode::from(self.add_node(tmp_true)).into());

                self.handle_require_inner(
                    ctx,
                    loc,
                    true_cvars,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                )?;
            }
            ExprRet::Multi(ref true_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                true_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_true(ctx, loc, expr_ret))?;
            }
        }
        Ok(())
    }

    fn match_yul_false(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        false_cvars: &ExprRet,
    ) -> Result<(), ExprErr> {
        match false_cvars {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc)?,
            ExprRet::Single(_false_cvar) | ExprRet::SingleLiteral(_false_cvar) => {
                // we wrap the conditional in an `iszero` to invert
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                        .into_expr_err(loc)?,
                );
                let rhs_paths =
                    ExprRet::Single(ContextVarNode::from(self.add_node(tmp_true)).into());

                self.handle_require_inner(
                    ctx,
                    loc,
                    false_cvars,
                    &rhs_paths,
                    RangeOp::Eq,
                    RangeOp::Neq,
                    (RangeOp::Neq, RangeOp::Eq),
                )?;
            }
            ExprRet::Multi(ref false_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                false_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_false(ctx, loc, expr_ret))?;
            }
        }

        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn yul_switch_stmt(
        &mut self,
        loc: Loc,
        condition: YulExpression,
        cases: Vec<YulSwitchOptions>,
        default: Option<YulSwitchOptions>,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let iec = IfElseChain::from(loc, (condition, cases, default))?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
            analyzer.yul_if_else(loc, &iec, ctx)
        })
        // let mut curr_statement: Option<YulStatement> = match default {
        //     Some(YulSwitchOptions::Default(_loc, block)) => {
        //         Some(YulStatement::Block(block))
        //     }
        //     Some(_) => unreachable!("case as default"),
        //     None => None,
        // };
        // let mut next_conditional = None;
        // let mut parts: Vec<(YulExpression, YulStatement, Option<YulExpression>, Option<YulStatement>)> = cases.iter().rev().map(|case| {
        //     match case {
        //         YulSwitchOptions::Case(loc, expr, stmt) => {
        //             let if_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
        //                 loc: *loc,
        //                 id: Identifier {
        //                     loc: *loc,
        //                     name: "eq".to_string(),
        //                 },
        //                 arguments: vec![condition.clone(), expr.clone()],
        //             }));
        //             if let Some(ref mut curr_statement) = &mut curr_statement {
        //                 // println!("{stmt:?}");
        //                 let true_stmt: YulStatement = YulStatement::If(*loc, if_expr.clone(), stmt.clone());
        //                 let false_conditional = next_conditional.take();
        //                 next_conditional = Some(if_expr.clone());
        //                 let ret = (if_expr, YulStatement::Block(stmt.clone()), false_conditional, Some(curr_statement.clone()));
        //                 *curr_statement = YulStatement::Block(YulBlock { loc: *loc, statements: vec![
        //                     true_stmt,
        //                     curr_statement.clone()
        //                 ]});
        //                 ret
        //             } else {
        //                 let true_stmt = YulStatement::If(*loc, if_expr.clone(), stmt.clone());
        //                 let ret = (if_expr, YulStatement::Block(stmt.clone()), None, None);
        //                 curr_statement = Some(true_stmt);
        //                 ret
        //             }
        //         }
        //         YulSwitchOptions::Default(_loc, _block) => {
        //             unreachable!("We shouldn't have a `default` case in cases - only in the `default` input parameter")
        //         }
        //     }
        // }).collect();
        // parts.reverse();

        // println!("{parts:#?}");

        // self.parse_ctx_yul_expr(&condition, ctx)?;
        // if parts.is_empty() {
        //     if let Some(curr_statement) = curr_statement {
        //         self.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
        //             analyzer.parse_ctx_yul_statement(&curr_statement, ctx);
        //             Ok(())
        //         })
        //     } else {
        //         Ok(())
        //     }
        //     // empty switch statement
        // } else {
        //     parts.iter().try_for_each(|(if_expr, true_stmt, false_expr, false_stmt)| {

        //     })
        // }
        // Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct IfElseChain {
    pub if_expr: YulExpression,
    pub true_stmt: YulStatement,
    pub next: Option<ElseOrDefault>,
}

#[derive(Clone, Debug)]
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
            return Err(ExprErr::NoRhs(loc, "No cases or default found for switch statement".to_string()))
        };

        let Some(iec) = IfElseChain::from_child(child) else {
            return Err(ExprErr::NoRhs(loc, "No cases or default found for switch statement".to_string()))
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
