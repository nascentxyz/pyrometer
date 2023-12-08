use crate::{env::Env, ContextBuilder, ExprErr, IntoExprErr};

use graph::{
    nodes::{ContextNode, ContextVar, ExprRet, VarNode},
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use solang_parser::pt::{Expression, Identifier};

impl<T> Variable for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

pub trait Variable: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
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

        // solang doesnt have `super` as a keyword
        if let Some(cvar) = ctx.var_by_name(self, &ident.name) {
            let cvar = cvar.latest_version(self);
            self.apply_to_edges(target_ctx, ident.loc, &|analyzer, edge_ctx, _loc| {
                let var = analyzer.advance_var_in_ctx(cvar, ident.loc, edge_ctx)?;
                edge_ctx
                    .push_expr(ExprRet::Single(var.into()), analyzer)
                    .into_expr_err(ident.loc)
            })
        } else if ident.name == "_" {
            self.env_variable(ident, target_ctx)?;
            Ok(())
        } else if let Some(cvar) = ctx
            .var_by_name_or_recurse(self, &ident.name)
            .into_expr_err(ident.loc)?
        {
            // check if we can inherit it
            let cvar = cvar.latest_version(self);
            self.apply_to_edges(target_ctx, ident.loc, &|analyzer, edge_ctx, _loc| {
                let var = analyzer.advance_var_in_ctx(cvar, ident.loc, edge_ctx)?;
                edge_ctx
                    .push_expr(ExprRet::Single(var.into()), analyzer)
                    .into_expr_err(ident.loc)
            })
            // if let Some(recursion_target) = recursion_target {
            //     self.variable(ident, parent_ctx, Some(recursion_target))
            // } else {
            //     self.variable(ident, parent_ctx, Some(target_ctx))
            // }
        } else if (self.env_variable(ident, target_ctx)?).is_some() {
            Ok(())
        } else if let Some(idx) = self.user_types().get(&ident.name).cloned() {
            let const_var = if let Node::Var(_v) = self.node(idx) {
                VarNode::from(idx)
                    .const_value(ident.loc, self)
                    .into_expr_err(ident.loc)?
            } else {
                None
            };

            let mut storage_idx = None;
            let var = if let Some(con) = const_var {
                con
            } else {
                match self.node(idx) {
                    Node::Var(_) => {
                        storage_idx = Some(idx);
                        match ContextVar::maybe_from_user_ty(self, ident.loc, idx) {
                            Some(v) => v,
                            None => {
                                return Err(ExprErr::VarBadType(
                                    ident.loc,
                                    format!(
                                        "Could not create context variable from user type: {:?}",
                                        self.node(idx)
                                    ),
                                ))
                            }
                        }
                    }
                    Node::Enum(_) => match ContextVar::maybe_from_user_ty(self, ident.loc, idx) {
                        Some(v) => v,
                        None => {
                            return Err(ExprErr::VarBadType(
                                ident.loc,
                                format!(
                                    "Could not create context variable from user type: {:?}",
                                    self.node(idx)
                                ),
                            ))
                        }
                    },
                    _ => {
                        return target_ctx
                            .push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(ident.loc)
                    }
                }
            };

            let new_cvarnode = self.add_node(Node::ContextVar(var));

            ctx.add_var(new_cvarnode.into(), self)
                .into_expr_err(ident.loc)?;

            if let Some(store_idx) = storage_idx {
                self.add_edge(
                    new_cvarnode,
                    store_idx,
                    Edge::Context(ContextEdge::InheritedStorageVariable),
                );
            }
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
