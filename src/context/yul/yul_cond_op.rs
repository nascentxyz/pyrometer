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

                analyzer.match_yul_true(ctx, &ret, if_expr)
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
            analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "True conditional had no lhs".to_string()));
                };

                analyzer.match_yul_false(ctx, &ret, if_expr)
            })
        })
    }

    fn match_yul_true(
        &mut self,
        ctx: ContextNode,
        true_cvars: &ExprRet,
        if_expr: &YulExpression,
    ) -> Result<(), ExprErr> {
        let loc = if_expr.loc();
        match true_cvars {
            ExprRet::CtxKilled => {}
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
                    .try_for_each(|expr_ret| self.match_yul_true(ctx, expr_ret, if_expr))?;
            }
        }
        Ok(())
    }

    fn match_yul_false(
        &mut self,
        ctx: ContextNode,
        false_cvars: &ExprRet,
        false_expr: &YulExpression,
    ) -> Result<(), ExprErr> {
        let loc = false_expr.loc();
        match false_cvars {
            ExprRet::CtxKilled => {}
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
                    .try_for_each(|expr_ret| self.match_yul_false(ctx, expr_ret, false_expr))?;
            }
        }

        Ok(())
    }
}
