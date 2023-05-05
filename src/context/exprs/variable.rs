use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::context::{exprs::env::Env, ContextBuilder};
use shared::{analyzer::AnalyzerLike, context::*, Edge, Node};
use solang_parser::pt::Expression;

use solang_parser::pt::Identifier;

impl<T> Variable for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}

pub trait Variable: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn variable(
        &mut self,
        ident: &Identifier,
        ctx: ContextNode,
        recursion_target: Option<ContextNode>,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "Getting variable: {}, loc: {:?}, ctx: {}",
            &ident.name,
            ident.loc,
            ctx.path(self)
        );
        let target_ctx = if let Some(recursion_target) = recursion_target {
            recursion_target
        } else {
            ctx
        };

        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            self.apply_to_edges(target_ctx, ident.loc, &|analyzer, edge_ctx, loc| {
                println!("HERE, {:?}", edge_ctx.underlying(analyzer).unwrap().child);
                let var = analyzer.advance_var_in_ctx(cvar, ident.loc, edge_ctx)?;
                edge_ctx
                    .push_expr(ExprRet::Single(var.into()), analyzer)
                    .into_expr_err(ident.loc)
            })
        } else if ident.name == "_" {
            self.env_variable(ident, target_ctx)?;
            Ok(())
        } else if let Some(parent_ctx) = ctx.underlying(self).into_expr_err(ident.loc)?.parent_ctx {
            // check if we can inherit it
            if let Some(recursion_target) = recursion_target {
                self.variable(ident, parent_ctx, Some(recursion_target))
            } else {
                self.variable(ident, parent_ctx, Some(target_ctx))
            }
        } else if (self.env_variable(ident, target_ctx)?).is_some() {
            Ok(())
        } else if let Some(idx) = self.user_types().get(&ident.name) {
            let var = match ContextVar::maybe_from_user_ty(self, ident.loc, *idx) {
                Some(v) => v,
                None => {
                    return Err(ExprErr::VarBadType(
                        ident.loc,
                        format!(
                            "Could not create context variable from user type: {:?}",
                            self.node(*idx)
                        ),
                    ))
                }
            };

            let new_cvarnode = self.add_node(Node::ContextVar(var));

            self.add_edge(
                new_cvarnode,
                target_ctx,
                Edge::Context(ContextEdge::Variable),
            );
            target_ctx
                .push_expr(ExprRet::Single(new_cvarnode), self)
                .into_expr_err(ident.loc)?;
            Ok(())
        } else if let Some(func_node) = self.builtin_fn_or_maybe_add(&ident.name) {
            target_ctx
                .push_expr(ExprRet::Single(func_node), self)
                .into_expr_err(ident.loc)?;
            Ok(())
        } else if let Some(_func) = target_ctx
            .visible_funcs(self)
            .into_expr_err(ident.loc)?
            .iter()
            .find(|func| func.name(self).unwrap() == ident.name)
        {
            Err(ExprErr::Todo(
                ident.loc,
                "Function as variables has limited support".to_string(),
            ))
        } else {
            let node = self.add_node(Node::Unresolved(ident.clone()));
            self.user_types_mut().insert(ident.name.clone(), node);
            target_ctx
                .push_expr(ExprRet::Single(node), self)
                .into_expr_err(ident.loc)?;
            Ok(())
        }
    }
}
