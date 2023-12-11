use crate::{assign::Assign, env::Env, ContextBuilder, ExprErr, IntoExprErr};

use graph::{
    nodes::{ContextVarNode, ContextNode, ContextVar, ExprRet, VarNode},
    GraphError, AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};

use solang_parser::pt::{VariableDeclaration, Loc, Expression, Identifier};

impl<T> Variable for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Deals with variable retrieval, parsing, and versioning
pub trait Variable: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Get a variable based on an identifier
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

    /// Match on the [`ExprRet`]s of a variable definition and construct the variable
    fn match_var_def(
        &mut self,
        ctx: ContextNode,
        var_decl: &VariableDeclaration,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: Option<&ExprRet>,
    ) -> Result<bool, ExprErr> {
        match (lhs_paths, rhs_paths) {
            (ExprRet::CtxKilled(kind), _) | (_, Some(ExprRet::CtxKilled(kind))) => {
                ctx.kill(self, loc, *kind).into_expr_err(loc)?;
                Ok(true)
            }
            (ExprRet::Single(ty), Some(ExprRet::SingleLiteral(rhs))) => {
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar.literal_cast_from_ty(ty, self).into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_var_def(
                    ctx,
                    var_decl,
                    loc,
                    lhs_paths,
                    Some(&ExprRet::Single(rhs_cvar.into())),
                )
            }
            (ExprRet::Single(ty), Some(ExprRet::Single(rhs))) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.as_ref().map(|s| s.clone().into()),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    is_return: false,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));
                let rhs = ContextVarNode::from(*rhs);

                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let _ = analyzer.assign(loc, lhs, rhs, ctx)?;
                    // match_assign_ret(analyzer, ctx, ret);
                    Ok(())
                })?;

                Ok(false)
            }
            (ExprRet::Single(ty), None) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.as_ref().map(|s| s.clone().into()),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    is_return: false,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));
                Ok(false)
            }
            (l @ ExprRet::Single(_lhs), Some(ExprRet::Multi(rhs_sides))) => Ok(rhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, l, Some(expr_ret)))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), r @ Some(ExprRet::Single(_))) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, expr_ret, r))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), None) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| self.match_var_def(ctx, var_decl, loc, expr_ret, None))
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), Some(ExprRet::Multi(rhs_sides))) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    Ok(lhs_sides
                        .iter()
                        .zip(rhs_sides.iter())
                        .map(|(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_var_def(ctx, var_decl, loc, lhs_expr_ret, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                } else {
                    Ok(rhs_sides
                        .iter()
                        .map(|rhs_expr_ret| {
                            self.match_var_def(ctx, var_decl, loc, lhs_paths, Some(rhs_expr_ret))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                }
            }
            (_e, _f) => Err(ExprErr::Todo(
                loc,
                "Unhandled ExprRet combination in `match_var_def`".to_string(),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    /// Creates a newer version of a variable in the context. It may or may not actually
    /// create this new variable depending on if there are two successively identical version.
    fn advance_var_in_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<ContextVarNode, ExprErr> {
        self.advance_var_in_ctx_forcible(cvar_node, loc, ctx, false)
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    /// Creates a new version of a variable in a context. Takes an additional parameter
    /// denoting whether or not to force the creation, skipping an optimization.
    fn advance_var_in_ctx_forcible(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
        force: bool,
    ) -> Result<ContextVarNode, ExprErr> {
        tracing::trace!(
            "advancing variable: {}",
            cvar_node.display_name(self).into_expr_err(loc)?
        );
        if let Some(cvar) = cvar_node.next_version(self) {
            panic!(
                "Not latest version of: {}",
                cvar.display_name(self).unwrap()
            );
        }
        if let Some(child) = ctx.underlying(self).into_expr_err(loc)?.child {
            return Err(ExprErr::GraphError(
                loc,
                GraphError::VariableUpdateInOldContext(format!(
                    "Variable update of {} in old context: parent: {}, child: {:#?}",
                    cvar_node.display_name(self).unwrap(),
                    ctx.path(self),
                    child
                )),
            ));
        }
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
        // get the old context
        let new_cvarnode;

        'a: {
            if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
                if !force {
                    // get the previous version to remove and prevent spurious nodes
                    if let Some(prev) = cvar_node.latest_version(self).previous_version(self) {
                        let prev_version = prev.underlying(self).into_expr_err(loc)?;
                        // check if there was no change between the previous version and the latest version
                        if prev_version.eq_ignore_loc(&new_cvar) && old_ctx == ctx {
                            // there was no change in the current context, just give them the current variable
                            new_cvarnode = cvar_node.into();
                            break 'a;
                        }
                    }
                }

                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
                if old_ctx != ctx {
                    ctx.add_var(new_cvarnode.into(), self).into_expr_err(loc)?;
                    self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(
                        new_cvarnode,
                        cvar_node.0,
                        Edge::Context(ContextEdge::InheritedVariable),
                    );
                } else {
                    self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
                }
            } else {
                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        }

        Ok(ContextVarNode::from(new_cvarnode))
    }

    /// Creates a new version of a variable in it's current context
    fn advance_var_in_curr_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        tracing::trace!(
            "advancing variable: {}",
            cvar_node.display_name(self).into_expr_err(loc)?
        );
        if let Some(cvar) = cvar_node.next_version(self) {
            panic!(
                "Not latest version of: {}",
                cvar.display_name(self).unwrap()
            );
        }
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
        new_cvar.loc = Some(loc);

        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));

        Ok(ContextVarNode::from(new_cvarnode))
    }

    /// Clones a variable and adds it to the graph
    fn advance_var_underlying(&mut self, cvar_node: ContextVarNode, loc: Loc) -> &mut ContextVar {
        assert_eq!(None, cvar_node.next_version(self));
        let mut new_cvar = cvar_node
            .latest_version(self)
            .underlying(self)
            .unwrap()
            .clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode)
            .underlying_mut(self)
            .unwrap()
    }
}
