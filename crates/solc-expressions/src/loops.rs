use crate::{variable::Variable, ContextBuilder, ExprErr, IntoExprErr, StatementParser};
use graph::ContextEdge;
use graph::Edge;

use graph::{
    nodes::{Context, ContextNode},
    AnalyzerBackend, GraphBackend, Node,
};

use solang_parser::pt::{Expression, Loc, Statement};

impl<T> Looper for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}

/// Dealing with loops
pub trait Looper:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    #[tracing::instrument(level = "trace", skip_all)]
    /// Handles a for loop. Needs improvement
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

    /// Resets all variables referenced in the loop because we don't elegantly handle loops
    fn reset_vars(&mut self, loc: Loc, ctx: ContextNode, body: &Statement) -> Result<(), ExprErr> {
        let og_ctx = ctx;
        let sctx = Context::new_loop_subctx(ctx, loc, self).into_expr_err(loc)?;
        let subctx = ContextNode::from(self.add_node(Node::Context(sctx)));
        ctx.set_child_call(subctx, self).into_expr_err(loc)?;
        self.add_edge(subctx, ctx, Edge::Context(ContextEdge::Loop));
        self.parse_ctx_statement(body, false, Some(subctx));
        self.apply_to_edges(subctx, loc, &|analyzer, ctx, loc| {
            let vars = subctx.local_vars(analyzer).clone();
            vars.iter().for_each(|(name, var)| {
                // widen to max range
                if let Some(inheritor_var) = ctx.var_by_name(analyzer, name) {
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

            let sctx =
                Context::new_subctx(ctx, Some(og_ctx), loc, None, None, false, analyzer, None)
                    .into_expr_err(loc)?;
            let sctx = ContextNode::from(analyzer.add_node(Node::Context(sctx)));
            ctx.set_child_call(sctx, analyzer).into_expr_err(loc)
        })
    }

    /// Handles a while-loop
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
