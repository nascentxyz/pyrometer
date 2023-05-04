use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{
    context::{exprs::env::Env, ContextBuilder},
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
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "Getting variable: {}, loc: {:?}, ctx: {}",
            &ident.name,
            ident.loc,
            ctx.path(self)
        );
        if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
            if let Some(recursion_target) = recursion_target {
                let var = self.advance_var_in_ctx(cvar, ident.loc, recursion_target)?;
                recursion_target.push_expr(ExprRet::Single(var.into()), self).into_expr_err(ident.loc)?;
                Ok(())
            } else {
                let var = self.advance_var_in_ctx(cvar, ident.loc, ctx)?;
                ctx.push_expr(ExprRet::Single(var.0.into()), self).into_expr_err(ident.loc)?;
                Ok(())
            }
        } else if ident.name == "_" {
            if let Some(recursion_target) = recursion_target {
                self.env_variable(ident, recursion_target)?;
            } else {
                self.env_variable(ident, ctx)?;
            }
            Ok(())
        } else if let Some(parent_ctx) = ctx.underlying(self).into_expr_err(ident.loc)?.parent_ctx {
            // check if we can inherit it
            if let Some(recursion_target) = recursion_target {
                self.variable(ident, parent_ctx, Some(recursion_target))
            } else {
                self.variable(ident, parent_ctx, Some(ctx))
            }
        } else if (self.env_variable(ident, ctx)?).is_some() {
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

            if let Some(recursion_target) = recursion_target {
                self.add_edge(new_cvarnode, recursion_target, Edge::Context(ContextEdge::Variable));
                recursion_target.push_expr(ExprRet::Single(new_cvarnode), self).into_expr_err(ident.loc)?;    
            }  else {
                self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(new_cvarnode), self).into_expr_err(ident.loc)?;  
            }
            
            Ok(())
        } else if let Some(func_node) = self.builtin_fn_or_maybe_add(&ident.name) {
            if let Some(recursion_target) = recursion_target {
                recursion_target.push_expr(ExprRet::Single(func_node), self).into_expr_err(ident.loc)?;
            } else {
                ctx.push_expr(ExprRet::Single(func_node), self).into_expr_err(ident.loc)?;
            }
            Ok(())
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
            if let Some(recursion_target) = recursion_target {
                let node = self.add_node(Node::Unresolved(ident.clone()));
                self.user_types_mut().insert(ident.name.clone(), node);
                recursion_target.push_expr(ExprRet::Single(node), self).into_expr_err(ident.loc)?;
            } else {
                let node = self.add_node(Node::Unresolved(ident.clone()));
                self.user_types_mut().insert(ident.name.clone(), node);
                ctx.push_expr(ExprRet::Single(node), self).into_expr_err(ident.loc)?;
            }
            Ok(())
        }
    }

    // fn match_variable(
    //     &mut self,
    //     ctx: ContextNode,
    //     ident: &Identifier,
    //     ret: ExprRet,
    // ) -> Result<(), ExprErr> {
    //     match ret {
    //         ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
    //             match self.node(cvar) {
    //                 Node::ContextVar(_) => {
    //                     let cvar = ContextVarNode::from(cvar).latest_version(self);
    //                     let mut ctx_cvar = self.advance_var_in_ctx(cvar, ident.loc, ctx)?;
    //                     ctx_cvar.update_deps(ctx, self).into_expr_err(ident.loc)?;
    //                     ctx.push_expr(ExprRet::Single(ctx_cvar.0.into()), self);
    //                     Ok(())
    //                 }
    //                 _ => {
    //                     ctx.push_expr(ExprRet::Single(cvar), self);
    //                     Ok(())
    //                 }
    //             }
    //         }
    //         ExprRet::Multi(inner) => {
    //             inner
    //                 .into_iter()
    //                 .try_for_each(|ret| self.match_variable(ctx, ident, ret))
    //         },
    //         ExprRet::CtxKilled => {
    //             ctx.push_expr(ExprRet::CtxKilled, self);
    //             Ok(())
    //         }
    //     }
    // }
}
