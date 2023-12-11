use crate::{require::Require, ContextBuilder, ExprErr, IntoExprErr, StatementParser, ExpressionParser};

use graph::{
    nodes::{Context, ContextNode},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::NodeIdx;

use solang_parser::pt::CodeLocation;
use solang_parser::pt::{Expression, Loc, Statement};

impl<T> CondOp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized
{}
/// Handles conditional operations, like `if .. else ..` and ternary operations
pub trait CondOp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Handles a conditional operation like `if .. else ..`
    fn cond_op_stmt(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_stmt: &Statement,
        false_stmt: &Option<Box<Statement>>,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let tctx =
                Context::new_subctx(ctx, None, loc, Some("true"), None, false, analyzer, None)
                    .into_expr_err(loc)?;
            let true_subctx = ContextNode::from(analyzer.add_node(Node::Context(tctx)));
            let fctx =
                Context::new_subctx(ctx, None, loc, Some("false"), None, false, analyzer, None)
                    .into_expr_err(loc)?;
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

            // we want to check if the true branch is possible to take
            analyzer.true_fork_if_cvar(if_expr.clone(), true_subctx)?;
            let mut true_killed = false;
            if true_subctx.is_killed(analyzer).into_expr_err(loc)?
                || true_subctx.unreachable(analyzer).into_expr_err(loc)?
            {
                // it was killed, therefore true branch is unreachable.
                // since it is unreachable, we want to not create
                // unnecessary subcontexts
                true_killed = true;
            }

            // we want to check if the false branch is possible to take
            analyzer.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
            let mut false_killed = false;
            if false_subctx.is_killed(analyzer).into_expr_err(loc)?
                || false_subctx.unreachable(analyzer).into_expr_err(loc)?
            {
                // it was killed, therefore true branch is unreachable.
                // since it is unreachable, we want to not create
                // unnecessary subcontexts
                false_killed = true;
            }

            match (true_killed, false_killed) {
                (true, true) => {
                    // both have been killed, delete the child and dont process the bodies
                    ctx.delete_child(analyzer).into_expr_err(loc)?;
                }
                (true, false) => {
                    // the true context has been killed, delete child, process the false fork expression
                    // in the parent context and parse the false body
                    ctx.delete_child(analyzer).into_expr_err(loc)?;
                    analyzer.false_fork_if_cvar(if_expr.clone(), ctx)?;
                    if let Some(false_stmt) = false_stmt {
                        return analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                            analyzer.parse_ctx_statement(false_stmt, false, Some(ctx));
                            Ok(())
                        });
                    }
                }
                (false, true) => {
                    // the false context has been killed, delete child, process the true fork expression
                    // in the parent context and parse the true body
                    ctx.delete_child(analyzer).into_expr_err(loc)?;
                    analyzer.true_fork_if_cvar(if_expr.clone(), ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                        analyzer.parse_ctx_statement(
                            true_stmt,
                            ctx.unchecked(analyzer).into_expr_err(loc)?,
                            Some(ctx),
                        );
                        Ok(())
                    })?;
                }
                (false, false) => {
                    // both branches are reachable. process each body
                    analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, _loc| {
                        analyzer.parse_ctx_statement(
                            true_stmt,
                            ctx.unchecked(analyzer).into_expr_err(loc)?,
                            Some(ctx),
                        );
                        Ok(())
                    })?;
                    if let Some(false_stmt) = false_stmt {
                        return analyzer.apply_to_edges(
                            false_subctx,
                            loc,
                            &|analyzer, ctx, _loc| {
                                analyzer.parse_ctx_statement(false_stmt, false, Some(ctx));
                                Ok(())
                            },
                        );
                    }
                }
            }
            Ok(())
        })
    }

    /// Handles a conditional expression like `if .. else ..`
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
            let tctx =
                Context::new_subctx(ctx, None, loc, Some("true"), None, false, analyzer, None)
                    .into_expr_err(loc)?;
            let true_subctx = ContextNode::from(analyzer.add_node(Node::Context(tctx)));
            let fctx =
                Context::new_subctx(ctx, None, loc, Some("false"), None, false, analyzer, None)
                    .into_expr_err(loc)?;
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

            analyzer.true_fork_if_cvar(if_expr.clone(), true_subctx)?;
            analyzer.apply_to_edges(true_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.parse_ctx_expr(true_expr, ctx)
            })?;

            analyzer.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
            analyzer.apply_to_edges(false_subctx, loc, &|analyzer, ctx, _loc| {
                analyzer.parse_ctx_expr(false_expr, ctx)
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
            analyzer.handle_require(&[if_expr.clone()], ctx)?;
            Ok(())
        })
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        false_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let loc = if_expr.loc();
        let inv_if_expr = self.inverse_expr(if_expr);
        self.apply_to_edges(false_fork_ctx, loc, &|analyzer, ctx, _loc| {
            analyzer.handle_require(&[inv_if_expr.clone()], ctx)?;
            Ok(())
        })
    }
}
