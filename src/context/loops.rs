use crate::context::exprs::IntoExprErr;
use crate::ExprErr;
use solang_parser::pt::Loc;
use solang_parser::pt::Statement;

use crate::context::ContextBuilder;
use shared::analyzer::GraphLike;
use shared::context::*;
use shared::{analyzer::AnalyzerLike, Edge, Node, NodeIdx};
use solang_parser::pt::Expression;

impl<T> Looper for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike {}
pub trait Looper: GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn for_loop(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        maybe_init: &Option<Box<Statement>>,
        _maybe_limiter: &Option<Box<Expression>>,
        _maybe_post: &Option<Box<Statement>>,
        maybe_body: &Option<Box<Statement>>,
    ) -> Result<(), ExprErr> {
        // TODO: improve this
        if let Some(initer) = maybe_init {
            self.parse_ctx_statement(initer, false, Some(ctx));
        }

        if let Some(body) = maybe_body {
            let subctx = ContextNode::from(self.add_node(Node::Context(
                Context::new_subctx(ctx, loc, false, None, false, self, None).into_expr_err(loc)?,
            )));
            ctx.add_child(subctx, self);
            let ctx_fork = self.add_node(Node::FunctionCall);
            self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
            self.add_edge(
                NodeIdx::from(subctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );
            self.parse_ctx_statement(body, false, Some(subctx));
            let vars = subctx.local_vars(self);
            vars.iter().for_each(|var| {
                // widen to max range
                if let Some(inheritor_var) = ctx.var_by_name(self, &var.name(self).unwrap()) {
                    let inheritor_var = inheritor_var.latest_version(self);
                    if let Some(r) = var
                        .underlying(self)
                        .unwrap()
                        .ty
                        .default_range(self)
                        .unwrap()
                    {
                        let new_inheritor_var = self.advance_var_in_ctx(inheritor_var, loc, ctx);
                        new_inheritor_var.set_range_min(self, r.min);
                        new_inheritor_var.set_range_max(self, r.max);
                    }
                }
            });
        }
        Ok(())
    }

    fn while_loop(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        _limiter: &Expression,
        body: &Statement,
    ) -> Result<(), ExprErr> {
        // TODO: improve this
        let subctx = ContextNode::from(self.add_node(Node::Context(
            Context::new_subctx(ctx, loc, false, None, false, self, None).into_expr_err(loc)?,
        )));
        ctx.add_child(subctx, self);
        let ctx_fork = self.add_node(Node::FunctionCall);
        self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
        self.add_edge(
            NodeIdx::from(subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        self.parse_ctx_statement(body, false, Some(subctx));
        let vars = subctx.local_vars(self);
        vars.iter().for_each(|var| {
            // widen to max range
            if let Some(inheritor_var) = ctx.var_by_name(self, &var.name(self).unwrap()) {
                let inheritor_var = inheritor_var.latest_version(self);
                if let Some(r) = var
                    .underlying(self)
                    .unwrap()
                    .ty
                    .default_range(self)
                    .unwrap()
                {
                    let new_inheritor_var = self.advance_var_in_ctx(inheritor_var, loc, ctx);
                    new_inheritor_var.set_range_min(self, r.min);
                    new_inheritor_var.set_range_max(self, r.max);
                }
            }
        });
        Ok(())
    }
}
