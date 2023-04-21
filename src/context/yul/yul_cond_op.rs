use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{exprs::Require, AnalyzerLike, ContextBuilder, ExprRet};
use shared::{context::*, Edge, Node, NodeIdx};

use solang_parser::pt::CodeLocation;
use solang_parser::pt::{Expression, Loc, Statement};

impl<T> CondOp for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized {}
pub trait CondOp: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn yul_cond_op_stmt(
        &mut self,
        loc: Loc,
        if_expr: &YulExpression,
        true_block: &YulBlock,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let true_subctx = ContextNode::from(self.add_node(Node::Context(
            Context::new_subctx(ctx, loc, true, None, false, self, None).into_expr_err(loc)?,
        )));
        ctx.add_fork(true_subctx, self).into_expr_err(loc)?;
        let false_subctx = ContextNode::from(self.add_node(Node::Context(
            Context::new_subctx(ctx, loc, true, None, false, self, None).into_expr_err(loc)?,
        )));
        ctx.add_fork(false_subctx, self).into_expr_err(loc)?;
        let ctx_fork = self.add_node(Node::ContextFork);
        self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::ContextFork));
        self.add_edge(
            NodeIdx::from(true_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        self.add_edge(
            NodeIdx::from(false_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );

        self.true_fork_if_cvar(if_expr.clone(), true_subctx)?;
        self.parse_ctx_yul_statement(YulStatement::Block(true_stmt), false, Some(true_subctx));
        self.false_fork_if_cvar(if_expr.clone(), false_subctx)?;

        Ok(())
    }

    fn match_yul_true(&mut self, true_cvars: &ExprRet, if_expr: &YulExpression) -> Result<(), ExprErr> {
        match true_cvars {
            ExprRet::CtxKilled => Ok(()),
            ExprRet::Single((fork_ctx, _true_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _true_cvar)) => {
                self.parse_ctx_yul_expr(if_expr, *fork_ctx)
            }
            ExprRet::Multi(ref true_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                true_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_true(expr_ret, if_expr))?;
                Ok(())
            }
            ExprRet::Fork(true_paths, other_true_paths) => {
                self.match_yul_true(true_paths, if_expr)?;
                self.match_yul_true(other_true_paths, if_expr)
            }
        }
    }

    fn match_yul_false(&mut self, false_cvars: &ExprRet, if_expr: &Expression) -> Result<(), ExprErr> {
        let loc = if_expr.loc();
        match false_cvars {
            ExprRet::CtxKilled => Ok(()),
            ExprRet::Single((fork_ctx, _false_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _false_cvar)) => {
                // we wrap the conditional in an `iszero` to invert
                self.parse_ctx_yul_expr(
                    YulExpression::FunctionCall(
                        YulFunctionCall {
                            loc,
                            id: Identifier { loc, name: "iszero" },
                            arguments: vec![if_expr.clone()],
                            *fork_ctx
                        }
                    )
                )
            }
            ExprRet::Multi(ref false_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                false_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_yul_false(expr_ret, if_expr))?;
                Ok(())
            }
            ExprRet::Fork(false_paths, other_false_paths) => {
                self.match_yul_false(false_paths, if_expr)?;
                self.match_yul_false(other_false_paths, if_expr)
            }
        }
    }
}
