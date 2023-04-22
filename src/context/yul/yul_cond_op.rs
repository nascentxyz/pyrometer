use crate::context::exprs::IntoExprErr;
use crate::context::yul::YulBuilder;
use crate::context::ExprErr;
use crate::Concrete;
use crate::ConcreteNode;
use crate::{exprs::Require, AnalyzerLike, ExprRet};
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

        let true_cvars = self.parse_ctx_yul_expr(if_expr, true_subctx)?;
        self.match_yul_true(&true_cvars, if_expr)?;
        self.parse_ctx_yul_statement(&YulStatement::Block(true_stmt.clone()), true_subctx);

        let false_expr = YulExpression::FunctionCall(Box::new(YulFunctionCall {
            loc,
            id: Identifier {
                loc,
                name: "iszero".to_string(),
            },
            arguments: vec![if_expr.clone()],
        }));
        let false_cvars = self.parse_ctx_yul_expr(&false_expr, false_subctx)?;
        self.match_yul_false(&false_cvars, &false_expr)?;

        Ok(())
    }

    fn match_yul_true(
        &mut self,
        true_cvars: &ExprRet,
        if_expr: &YulExpression,
    ) -> Result<(), ExprErr> {
        let loc = if_expr.loc();
        match true_cvars {
            ExprRet::CtxKilled => {}
            ExprRet::Single((fork_ctx, _true_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _true_cvar)) => {
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, cnode, self).into_expr_err(loc)?,
                );
                let rhs_paths = ExprRet::Single((
                    *fork_ctx,
                    ContextVarNode::from(self.add_node(tmp_true)).into(),
                ));

                self.handle_require_inner(
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
                    .try_for_each(|expr_ret| self.match_yul_true(expr_ret, if_expr))?;
            }
            ExprRet::Fork(true_paths, other_true_paths) => {
                self.match_yul_true(true_paths, if_expr)?;
                self.match_yul_true(other_true_paths, if_expr)?;
            }
        }
        Ok(())
    }

    fn match_yul_false(
        &mut self,
        false_cvars: &ExprRet,
        false_expr: &YulExpression,
    ) -> Result<(), ExprErr> {
        let loc = false_expr.loc();
        match false_cvars {
            ExprRet::CtxKilled => {}
            ExprRet::Single((fork_ctx, _false_cvar))
            | ExprRet::SingleLiteral((fork_ctx, _false_cvar)) => {
                // we wrap the conditional in an `iszero` to invert
                let cnode = ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Bool(true))));
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, cnode, self).into_expr_err(loc)?,
                );
                let rhs_paths = ExprRet::Single((
                    *fork_ctx,
                    ContextVarNode::from(self.add_node(tmp_true)).into(),
                ));

                self.handle_require_inner(
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
                    .try_for_each(|expr_ret| self.match_yul_false(expr_ret, false_expr))?;
            }
            ExprRet::Fork(false_paths, other_false_paths) => {
                self.match_yul_false(false_paths, false_expr)?;
                self.match_yul_false(other_false_paths, false_expr)?;
            }
        }

        Ok(())
    }
}
