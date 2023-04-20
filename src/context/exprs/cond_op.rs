use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{exprs::Require, AnalyzerLike, ContextBuilder, ExprRet};
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

        // println!("true_stmt: {true_stmt:#?}");

        self.true_fork_if_cvar(if_expr.clone(), true_subctx)?;
        // println!("\n\n HERE: {:?} \n\n", true_subctx.killed_loc(self));
        self.parse_ctx_statement(true_stmt, false, Some(true_subctx));

        if let Some(false_stmt) = false_stmt {
            self.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
            self.parse_ctx_statement(false_stmt, false, Some(false_subctx));
        } else {
            self.false_fork_if_cvar(if_expr.clone(), false_subctx)?;
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
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!("conditional operator");
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

        let true_cvars = self.parse_ctx_expr(true_expr, true_subctx)?;
        self.match_true(&true_cvars, if_expr)?;

        let false_cvars = self.parse_ctx_expr(false_expr, false_subctx)?;
        self.match_false(&false_cvars, if_expr)?;

        Ok(ExprRet::Fork(Box::new(true_cvars), Box::new(false_cvars)))
    }

    fn match_true(&mut self, true_cvars: &ExprRet, if_expr: &Expression) -> Result<(), ExprErr> {
        match true_cvars {
            ExprRet::CtxKilled => Ok(()),
            ExprRet::Single((fork_ctx, _true_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _true_cvar)) => {
                self.true_fork_if_cvar(if_expr.clone(), *fork_ctx)
            }
            ExprRet::Multi(ref true_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                true_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_true(expr_ret, if_expr))?;
                Ok(())
            }
            ExprRet::Fork(true_paths, other_true_paths) => {
                self.match_true(true_paths, if_expr)?;
                self.match_true(other_true_paths, if_expr)
            }
        }
    }

    fn match_false(&mut self, false_cvars: &ExprRet, if_expr: &Expression) -> Result<(), ExprErr> {
        match false_cvars {
            ExprRet::CtxKilled => Ok(()),
            ExprRet::Single((fork_ctx, _false_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _false_cvar)) => {
                self.false_fork_if_cvar(if_expr.clone(), *fork_ctx)
            }
            ExprRet::Multi(ref false_paths) => {
                // TODO: validate this
                // we only take one because we just need the context out of the return
                false_paths
                    .iter()
                    .take(1)
                    .try_for_each(|expr_ret| self.match_false(expr_ret, if_expr))?;
                Ok(())
            }
            ExprRet::Fork(false_paths, other_false_paths) => {
                self.match_false(false_paths, if_expr)?;
                self.match_false(other_false_paths, if_expr)
            }
        }
    }

    /// Creates the true_fork cvar (updates bounds assuming its true)
    fn true_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        true_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let if_expr = match if_expr {
            Expression::Equal(loc, lhs, rhs) => Expression::Equal(loc, lhs, rhs),
            Expression::And(loc, lhs, rhs) => Expression::And(loc, lhs, rhs),
            Expression::Or(loc, lhs, rhs) => Expression::Or(loc, lhs, rhs),
            Expression::Not(loc, lhs) => Expression::Not(loc, lhs),
            Expression::NotEqual(loc, lhs, rhs) => Expression::NotEqual(loc, lhs, rhs),
            Expression::Less(loc, lhs, rhs) => Expression::Less(loc, lhs, rhs),
            Expression::More(loc, lhs, rhs) => Expression::More(loc, lhs, rhs),
            Expression::MoreEqual(loc, lhs, rhs) => Expression::MoreEqual(loc, lhs, rhs),
            Expression::LessEqual(loc, lhs, rhs) => Expression::LessEqual(loc, lhs, rhs),
            Expression::Variable(ref ident) => Expression::Variable(ident.clone()),
            e => e,
        };
        // println!("true fork if: {if_expr:?} {true_fork_ctx:?}");
        self.handle_require(&[if_expr], true_fork_ctx)
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(
        &mut self,
        if_expr: Expression,
        false_fork_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let inv_if_expr = match if_expr {
            Expression::Equal(loc, lhs, rhs) => Expression::NotEqual(loc, lhs, rhs),
            Expression::NotEqual(loc, lhs, rhs) => Expression::Equal(loc, lhs, rhs),
            Expression::Less(loc, lhs, rhs) => Expression::MoreEqual(loc, lhs, rhs),
            Expression::More(loc, lhs, rhs) => Expression::LessEqual(loc, lhs, rhs),
            Expression::MoreEqual(loc, lhs, rhs) => Expression::Less(loc, lhs, rhs),
            Expression::LessEqual(loc, lhs, rhs) => Expression::More(loc, lhs, rhs),
            Expression::Variable(ref ident) => Expression::Not(ident.loc, Box::new(if_expr)),
            e => Expression::Not(e.loc(), Box::new(e)),
        };
        // println!("inverse if expr: {inv_if_expr:?}");
        self.handle_require(&[inv_if_expr], false_fork_ctx)
    }
}
