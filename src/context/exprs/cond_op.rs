use crate::{exprs::Require, AnalyzerLike, ContextBuilder, ExprRet};
use shared::{context::*, Edge, Node, NodeIdx};

use solang_parser::pt::CodeLocation;
use solang_parser::pt::{Expression, Loc, Statement};

impl<T> CondOp for T where T: AnalyzerLike<Expr = Expression> + Require + Sized {}
pub trait CondOp: AnalyzerLike<Expr = Expression> + Require + Sized {
    fn cond_op_stmt(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_stmt: &Statement,
        false_stmt: &Option<Box<Statement>>,
        ctx: ContextNode,
    ) {
        let true_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            ctx, loc, true, None, false, self, None,
        ))));
        ctx.add_fork(true_subctx, self);
        let false_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            ctx, loc, true, None, false, self, None,
        ))));
        ctx.add_fork(false_subctx, self);
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

        self.true_fork_if_cvar(true_stmt.loc(), if_expr.clone(), true_subctx);
        self.parse_ctx_statement(true_stmt, false, Some(true_subctx));

        if let Some(false_stmt) = false_stmt {
            self.false_fork_if_cvar(false_stmt.loc(), if_expr.clone(), false_subctx);
            self.parse_ctx_statement(false_stmt, false, Some(false_subctx));
        }
    }

    /// When we have a conditional operator, we create a fork in the context. One side of the fork is
    /// if the expression is true, the other is if it is false.
    fn cond_op_expr(
        &mut self,
        loc: Loc,
        if_expr: &Expression,
        true_expr: &Expression,
        false_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let true_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            ctx, loc, true, None, false, self, None,
        ))));
        ctx.add_fork(true_subctx, self);
        let false_subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            ctx, loc, true, None, false, self, None,
        ))));
        ctx.add_fork(false_subctx, self);
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

        let true_loc = true_expr.loc();
        let true_cvars = self.parse_ctx_expr(true_expr, true_subctx);
        self.match_true(true_loc, &true_cvars, if_expr);

        let false_loc = false_expr.loc();
        let false_cvars = self.parse_ctx_expr(false_expr, false_subctx);
        self.match_false(false_loc, &false_cvars, if_expr);

        ExprRet::Fork(Box::new(true_cvars), Box::new(false_cvars))
    }

    fn match_true(&mut self, loc: Loc, true_cvars: &ExprRet, if_expr: &Expression) {
        match true_cvars {
            ExprRet::CtxKilled => {}
            ExprRet::Single((fork_ctx, _true_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _true_cvar)) => {
                self.true_fork_if_cvar(loc, if_expr.clone(), *fork_ctx);
            }
            ExprRet::Multi(ref true_paths) => true_paths.iter().take(1).for_each(|expr_ret| {
                let (fork_ctx, _) = expr_ret.expect_single();
                self.true_fork_if_cvar(loc, if_expr.clone(), fork_ctx);
            }),
            ExprRet::Fork(true_paths, other_true_paths) => {
                self.match_true(loc, true_paths, if_expr);
                self.match_true(loc, other_true_paths, if_expr);
            }
        }
    }

    fn match_false(&mut self, loc: Loc, false_cvars: &ExprRet, if_expr: &Expression) {
        match false_cvars {
            ExprRet::CtxKilled => {}
            ExprRet::Single((fork_ctx, _false_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _false_cvar)) => {
                self.false_fork_if_cvar(loc, if_expr.clone(), *fork_ctx);
            }
            ExprRet::Multi(ref false_paths) => false_paths.iter().take(1).for_each(|expr_ret| {
                let (fork_ctx, _) = expr_ret.expect_single();
                self.false_fork_if_cvar(loc, if_expr.clone(), fork_ctx);
            }),
            ExprRet::Fork(false_paths, other_false_paths) => {
                self.match_false(loc, false_paths, if_expr);
                self.match_false(loc, other_false_paths, if_expr);
            }
        }
    }

    /// Creates the true_fork cvar (updates bounds assuming its true)
    fn true_fork_if_cvar(&mut self, loc: Loc, if_expr: Expression, true_fork_ctx: ContextNode) {
        let if_expr = match if_expr {
            Expression::Equal(_loc, lhs, rhs) => Expression::Equal(loc, lhs, rhs),
            Expression::And(_loc, lhs, rhs) => Expression::And(loc, lhs, rhs),
            Expression::NotEqual(_loc, lhs, rhs) => Expression::NotEqual(loc, lhs, rhs),
            Expression::Less(_loc, lhs, rhs) => Expression::Less(loc, lhs, rhs),
            Expression::More(_loc, lhs, rhs) => Expression::More(loc, lhs, rhs),
            Expression::MoreEqual(_loc, lhs, rhs) => Expression::MoreEqual(loc, lhs, rhs),
            Expression::LessEqual(_loc, lhs, rhs) => Expression::LessEqual(loc, lhs, rhs),
            Expression::Variable(ref ident) => {
                let mut c = ident.clone();
                c.loc = loc;
                Expression::Variable(c)
            }
            e => todo!("Wasnt comparator: {:?}", e),
        };
        // println!("true fork if: {if_expr:?} {true_fork_ctx:?}");
        self.handle_require(&[if_expr], true_fork_ctx)
    }

    /// Creates the false_fork cvar (inverts the expression and sets the bounds assuming its false)
    fn false_fork_if_cvar(&mut self, loc: Loc, if_expr: Expression, false_fork_ctx: ContextNode) {
        let inv_if_expr = match if_expr {
            Expression::Equal(_loc, lhs, rhs) => Expression::NotEqual(loc, lhs, rhs),
            Expression::NotEqual(_loc, lhs, rhs) => Expression::Equal(loc, lhs, rhs),
            Expression::Less(_loc, lhs, rhs) => Expression::MoreEqual(loc, lhs, rhs),
            Expression::More(_loc, lhs, rhs) => Expression::LessEqual(loc, lhs, rhs),
            Expression::MoreEqual(_loc, lhs, rhs) => Expression::Less(loc, lhs, rhs),
            Expression::LessEqual(_loc, lhs, rhs) => Expression::More(loc, lhs, rhs),
            Expression::Variable(ref _ident) => Expression::Not(loc, Box::new(if_expr)),
            e => todo!("Wasnt comparator: {:?}", e),
        };
        // println!("inverse if expr: {inv_if_expr:?}");
        self.handle_require(&[inv_if_expr], false_fork_ctx)
    }
}
