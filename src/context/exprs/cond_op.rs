use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{exprs::Require, AnalyzerLike, ContextBuilder};
use shared::{context::*, Edge, Node, NodeIdx};

use solang_parser::pt::CodeLocation;
use solang_parser::pt::{Expression, Loc, Statement};

impl<T> CondOp for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized {}
pub trait CondOp: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Require + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn cond_op_stmt(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_stmt: &Statement,
        false_stmt: &Option<Box<Statement>>,
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

            analyzer.parse_ctx_statement(true_stmt, false, Some(true_subctx));
            analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.true_fork_if_cvar(if_expr.clone(), ctx)
            })?;

            if let Some(false_stmt) = false_stmt {
                analyzer.parse_ctx_statement(false_stmt, false, Some(false_subctx));
            }

            analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.false_fork_if_cvar(if_expr.clone(), ctx)
            })
        })
    }

    /// When we have a conditional operator, we create a fork in the context. One side of the fork is
    /// if the expression is true, the other is if it is false.
    #[tracing::instrument(level = "trace", skip_all)]
    fn cond_op_expr(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_expr: &Expression,
        false_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        tracing::trace!("conditional operator");
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

            analyzer.parse_ctx_expr(true_expr, true_subctx)?;
            analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.true_fork_if_cvar(if_expr.clone(), ctx)
            })?;

            analyzer.parse_ctx_expr(false_expr, false_subctx)?;
            analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.false_fork_if_cvar(if_expr.clone(), ctx)
            })
        })
    }

    /// Creates the true_fork cvar (updates bounds assuming its true)
    fn true_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        true_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(true_fork_ctx, if_expr.loc(), &|analyzer, ctx, _loc| {
            analyzer.handle_require(&[if_expr.clone()], ctx)
        })
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        false_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let loc = if_expr.loc();
        let inv_if_expr = Expression::Not(loc, Box::new(if_expr));
        // println!("inverse if expr: {inv_if_expr:?}");
        self.apply_to_edges(false_fork_ctx, loc, &|analyzer, ctx, _loc| {
            analyzer.handle_require(&[inv_if_expr.clone()], ctx)
        })
    }
}
