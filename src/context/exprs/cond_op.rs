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
        let true_subctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(ctx, None, loc, Some("true"), None, false, self, None)
                    .into_expr_err(loc)?,
            )),
        );
        let false_subctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(ctx, None, loc, Some("false"), None, false, self, None)
                    .into_expr_err(loc)?,
            )),
        );
        ctx.set_child_fork(true_subctx, false_subctx, self)
            .into_expr_err(loc)?;
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
        self.parse_ctx_statement(true_stmt, false, Some(true_subctx));

        self.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
        if let Some(false_stmt) = false_stmt {
            self.parse_ctx_statement(false_stmt, false, Some(false_subctx));
        }

        Ok(())
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
        let true_subctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(ctx, None, loc, Some("true"), None, false, self, None)
                    .into_expr_err(loc)?,
            )),
        );
        let false_subctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(ctx, None, loc, Some("false"), None, false, self, None)
                    .into_expr_err(loc)?,
            )),
        );
        ctx.set_child_fork(true_subctx, false_subctx, self)
            .into_expr_err(loc)?;
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
        self.parse_ctx_expr(true_expr, true_subctx)?;

        self.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
        self.parse_ctx_expr(false_expr, false_subctx)?;

        Ok(())
    }

    /// Creates the true_fork cvar (updates bounds assuming its true)
    fn true_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        true_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.handle_require(&[if_expr], true_fork_ctx)
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        false_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let inv_if_expr = Expression::Not(if_expr.loc(), Box::new(if_expr));
        // println!("inverse if expr: {inv_if_expr:?}");
        self.handle_require(&[inv_if_expr], false_fork_ctx)
    }
}
