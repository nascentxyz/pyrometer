use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{
    context::{exprs::env::Env, ContextBuilder},
    ExprRet,
};
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
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "Getting variable: {}, loc: {:?}, ctx: {}",
            &ident.name,
            ident.loc,
            ctx.path(self)
        );
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            if recursion_target.is_some() {
                Ok(ExprRet::Single((ctx, cvar.into())))
            } else {
                let var = self.advance_var_in_ctx(cvar, ident.loc, ctx)?;
                Ok(ExprRet::Single((ctx, var.0.into())))
            }
        } else if ident.name == "_" {
            tracing::trace!("Warning: got _, must be in modifier");
            if let Some(env) = self.env_variable(ident, ctx)? {
                Ok(env)
            } else {
                // if we've reached this point, we are evaluating a modifier and it was the "_" keyword
                Ok(ExprRet::Multi(vec![]))
            }
        } else if let Some(parent_ctx) = ctx.underlying(self).into_expr_err(ident.loc)?.parent_ctx {
            // check if we can inherit it
            if let Some(recursion_target) = recursion_target {
                self.variable(ident, parent_ctx, Some(recursion_target))
            } else {
                let ret = self.variable(ident, parent_ctx, Some(ctx))?;
                self.match_variable(ctx, ident, ret)
            }
        } else if let Some(env) = self.env_variable(ident, ctx)? {
            Ok(env)
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
        } else if let Some(func_node) = self.builtin_fn_or_maybe_add(&ident.name) {
            Ok(ExprRet::Single((ctx, func_node)))
        } else if let Some(_func) = ctx
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
            Ok(ExprRet::Single((ctx, node)))
        }
    }

    fn match_variable(
        &mut self,
        ctx: ContextNode,
        ident: &Identifier,
        ret: ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Single((_pctx, cvar)) | ExprRet::SingleLiteral((_pctx, cvar)) => {
                match self.node(cvar) {
                    Node::ContextVar(_) => {
                        let cvar = ContextVarNode::from(cvar).latest_version(self);
                        let mut ctx_cvar = self.advance_var_in_ctx(cvar, ident.loc, ctx)?;
                        ctx_cvar.update_deps(ctx, self).into_expr_err(ident.loc)?;
                        Ok(ExprRet::Single((ctx, ctx_cvar.0.into())))
                    }
                    _ => Ok(ExprRet::Single((ctx, cvar))),
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|ret| self.match_variable(ctx, ident, ret))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_variable(ctx, ident, *w1)?),
                Box::new(self.match_variable(ctx, ident, *w2)?),
            )),
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
        }
    }
}
