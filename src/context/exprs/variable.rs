use crate::context::ExprErr;
use crate::{
    context::{exprs::env::Env, ContextBuilder},
    ExprRet,
};
use shared::{analyzer::AnalyzerLike, context::*, range::Range, Edge, Node};
use solang_parser::pt::Expression;

use solang_parser::pt::Identifier;

impl<T> Variable for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}

pub trait Variable: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn variable(&mut self, ident: &Identifier, ctx: ContextNode) -> Result<ExprRet, ExprErr> {
        tracing::trace!("Getting variable: {}, loc: {:?}", &ident.name, ident.loc);
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            let var = self.advance_var_in_ctx(cvar, ident.loc, ctx);
            Ok(ExprRet::Single((ctx, var.0.into())))
        } else if let Some(env) = self.env_variable(ident, ctx)? {
            Ok(env)
        } else if ident.name == "_" {
            // if we've reached this point, we are evaluating a modifier and it was the "_" keyword
            Ok(ExprRet::Multi(vec![]))
        } else if let Some(parent_ctx) = ctx.underlying(self).parent_ctx {
            // check if we can inherit it
            let (_pctx, cvar) = self.variable(ident, parent_ctx)?.expect_single(ident.loc)?;
            match self.node(cvar) {
                Node::ContextVar(_) => {
                    let cvar = ContextVarNode::from(cvar).latest_version(self);
                    let mut ctx_cvar = self.advance_var_in_ctx(cvar, ident.loc, ctx);
                    ctx_cvar.update_deps(ctx, self);
                    Ok(ExprRet::Single((ctx, ctx_cvar.0.into())))
                }
                _ => Ok(ExprRet::Single((ctx, cvar))),
            }
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
            self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
            Ok(ExprRet::Single((ctx, new_cvarnode)))
        } else if let Some(func) = self.builtin_fns().get(&ident.name) {
            let (inputs, outputs) = self
                .builtin_fn_inputs()
                .get(&ident.name)
                .expect("builtin func but no inputs")
                .clone();
            let func_node = self.add_node(Node::Function(func.clone()));
            inputs.into_iter().for_each(|input| {
                let input_node = self.add_node(input);
                self.add_edge(input_node, func_node, Edge::FunctionParam);
            });
            outputs.into_iter().for_each(|output| {
                let output_node = self.add_node(output);
                self.add_edge(output_node, func_node, Edge::FunctionReturn);
            });
            Ok(ExprRet::Single((ctx, func_node)))
        } else if let Some(_func) = ctx
            .visible_funcs(self)
            .iter()
            .find(|func| func.name(self) == ident.name)
        {
            Err(ExprErr::Todo(
                ident.loc,
                "Function as variables has limited support".to_string(),
            ))
        } else {
            let node = self.add_node(Node::Unresolved(ident.clone()));
            self.user_types_mut().insert(ident.name.clone(), node);
            Ok(ExprRet::Single((ctx, node)))
        }
    }
}
