use crate::context::exprs::IntoExprErr;
use crate::ExprErr;
use solang_parser::pt::Loc;
use solang_parser::pt::Statement;

use crate::context::ContextBuilder;
use shared::analyzer::GraphLike;
use shared::context::*;
use shared::{analyzer::AnalyzerLike, Node};
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
            self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                analyzer.reset_vars(loc, ctx, body)
            })
        } else {
            Ok(())
        }
    }

    fn reset_vars(&mut self, loc: Loc, ctx: ContextNode, body: &Statement) -> Result<(), ExprErr> {
        let subctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(ctx, None, loc, None, None, false, self, None)
                    .into_expr_err(loc)?,
            )),
        );
        // let res = ctx.set_child_call(subctx, self).into_expr_err(loc);
        // let _ = self.add_if_err(res);
        // let ctx_fork = self.add_node(Node::FunctionCall);
        // self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
        // self.add_edge(
        //     NodeIdx::from(subctx.0),
        //     ctx_fork,
        //     Edge::Context(ContextEdge::Subcontext),
        // );
        self.parse_ctx_statement(body, false, Some(subctx));
        self.apply_to_edges(subctx, loc, &|analyzer, subctx, loc| {
            let vars = subctx.local_vars(analyzer);
            vars.iter().for_each(|var| {
                // widen to max range
                if let Some(inheritor_var) = ctx.var_by_name(analyzer, &var.name(analyzer).unwrap())
                {
                    let inheritor_var = inheritor_var.latest_version(analyzer);
                    if let Some(r) = var
                        .underlying(analyzer)
                        .unwrap()
                        .ty
                        .default_range(analyzer)
                        .unwrap()
                    {
                        let new_inheritor_var = analyzer
                            .advance_var_in_ctx(inheritor_var, loc, ctx)
                            .unwrap();
                        let res = new_inheritor_var
                            .set_range_min(analyzer, r.min)
                            .into_expr_err(loc);
                        let _ = analyzer.add_if_err(res);
                        let res = new_inheritor_var
                            .set_range_max(analyzer, r.max)
                            .into_expr_err(loc);
                        let _ = analyzer.add_if_err(res);
                    }
                }
            });
            Ok(())
        })
    }

    fn while_loop(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        _limiter: &Expression,
        body: &Statement,
    ) -> Result<(), ExprErr> {
        // TODO: improve this
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            analyzer.reset_vars(loc, ctx, body)
        })
    }
}
