use crate::{assign::Assign, env::Env, ContextBuilder};

use graph::{
    elem::Elem,
    nodes::{Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, VarNode},
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};
use shared::{ExprErr, GraphError, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Identifier, Loc, StorageLocation};

impl<T> Variable for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Deals with variable retrieval, parsing, and versioning
pub trait Variable: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Get a variable based on an identifier
    fn variable(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ident: &Identifier,
        ctx: ContextNode,
        location: Option<StorageLocation>,
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
            let cvar = cvar.latest_version_or_inherited_in_ctx(ctx, self);
            self.apply_to_edges(
                target_ctx,
                ident.loc,
                arena,
                &|analyzer, _arena, edge_ctx, _loc| {
                    let var = analyzer.advance_var_in_ctx(cvar, ident.loc, edge_ctx)?;
                    edge_ctx
                        .push_expr(ExprRet::Single(var.into()), analyzer)
                        .into_expr_err(ident.loc)
                },
            )
        } else if ident.name == "_" {
            self.env_variable(arena, ident, target_ctx)?;
            Ok(())
        } else if let Some(cvar) = ctx
            .var_by_name_or_recurse(self, &ident.name)
            .into_expr_err(ident.loc)?
        {
            // check if we can inherit it
            let cvar = cvar.latest_version_or_inherited_in_ctx(ctx, self);
            self.apply_to_edges(
                target_ctx,
                ident.loc,
                arena,
                &|analyzer, _arena, edge_ctx, _loc| {
                    let var = analyzer.advance_var_in_ctx(cvar, ident.loc, edge_ctx)?;
                    edge_ctx
                        .push_expr(ExprRet::Single(var.into()), analyzer)
                        .into_expr_err(ident.loc)
                },
            )
            // if let Some(recursion_target) = recursion_target {
            //     self.variable(ident, parent_ctx, Some(recursion_target))
            // } else {
            //     self.variable(ident, parent_ctx, Some(target_ctx))
            // }
        } else if (self.env_variable(arena, ident, target_ctx)?).is_some() {
            Ok(())
        } else if let Some(idxs) = self.user_types().get(&ident.name).cloned() {
            tracing::trace!("Getting variable via user_types");
            let idx = if idxs.len() == 1 {
                idxs[0]
            } else {
                // disambiguate by scope
                tracing::trace!("disambiguating by scope");
                let in_scope = if let Some(contract) = ctx
                    .maybe_associated_contract(self)
                    .into_expr_err(ident.loc)?
                {
                    let mut all_storage_vars_tys = contract
                        .all_storage_vars(self)
                        .iter()
                        .map(|i| i.0.into())
                        .collect::<Vec<_>>();
                    all_storage_vars_tys.sort();
                    all_storage_vars_tys.dedup();
                    all_storage_vars_tys
                } else {
                    vec![]
                };
                if let Some(idx) = self.disambiguate(ctx, idxs, in_scope, location) {
                    idx
                } else {
                    return Err(ExprErr::ParseError(
                        ident.loc,
                        "Unable to disambiguate variable".to_string(),
                    ));
                }
            };

            let mut is_contract_var = false;
            let const_var = if let Node::Var(_v) = self.node(idx) {
                is_contract_var = true;
                VarNode::from(idx)
                    .const_value(ident.loc, self)
                    .into_expr_err(ident.loc)?
            } else {
                None
            };

            let var = if let Some(con) = const_var {
                con
            } else {
                match self.node(idx) {
                    Node::Var(_) | Node::Enum(_) => {
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
                    _ => {
                        return target_ctx
                            .push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(ident.loc)
                    }
                }
            };

            let new_cvarnode = self.add_node(var);

            ctx.add_var(new_cvarnode.into(), self)
                .into_expr_err(ident.loc)?;
            self.add_edge(
                new_cvarnode,
                target_ctx,
                Edge::Context(ContextEdge::Variable),
            );

            if is_contract_var {
                self.add_edge(
                    new_cvarnode,
                    idx,
                    Edge::Context(ContextEdge::ContractVariable),
                );
            }

            if let Some(strukt) = ContextVarNode::from(new_cvarnode)
                .maybe_struct(self)
                .into_expr_err(ident.loc)?
            {
                strukt
                    .add_fields_to_cvar(self, ident.loc, ContextVarNode::from(new_cvarnode))
                    .into_expr_err(ident.loc)?;
            }

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
            let entry = self.user_types_mut().entry(ident.name.clone()).or_default();
            entry.push(node);
            target_ctx
                .push_expr(ExprRet::Single(node), self)
                .into_expr_err(ident.loc)?;
            Ok(())
        }
    }

    fn disambiguate(
        &mut self,
        ctx: ContextNode,
        mut idxs: Vec<NodeIdx>,
        inscope_storage: Vec<NodeIdx>,
        location: Option<StorageLocation>,
    ) -> Option<NodeIdx> {
        // disambiguate based on left hand side if it exists
        if let Some(maybe_lhs) = ctx.underlying(self).ok()?.expr_ret_stack.first() {
            tracing::trace!("Disambiguate based on lhs: {}", maybe_lhs.debug_str(self));
            if let ExprRet::Single(lhs_idx) = maybe_lhs {
                if let Some(var_ty) = VarType::try_from_idx(self, *lhs_idx) {
                    if idxs.contains(&var_ty.ty_idx()) {
                        return Some(var_ty.ty_idx());
                    }
                }
            }
        }

        // disambiguate based on storage location
        match location {
            Some(StorageLocation::Storage(..)) => {
                let mut idxs = idxs.clone();
                idxs.retain(|i| inscope_storage.contains(i));
                return match idxs.len() {
                    1 => Some(idxs[0]),
                    2 => {
                        // solidity is weird where if the current contract shadows a struct definition in a storage variable,
                        // the struct is presumed the correct type.
                        // ```
                        // contract B {
                        //     struct A {}
                        // }
                        // contract A is B {
                        //     A a;
                        //     function foo() external {
                        //         // a is of type B.A, *not* Contract::A
                        //         a = A(address(this));
                        //     }
                        // }
                        // ```
                        match (self.node(idxs[0]), self.node(idxs[1])) {
                            (Node::Contract(..), Node::Struct(..)) => Some(idxs[1]),
                            (Node::Struct(..), Node::Contract(..)) => Some(idxs[0]),
                            _ => None,
                        }
                    }
                    _ => None,
                };
            }
            Some(StorageLocation::Memory(..)) | Some(StorageLocation::Calldata(..)) => idxs
                .iter()
                .find(|idx| matches!(self.node(**idx), Node::Struct(..)))
                .copied(),
            None => {
                let t = &mut idxs;
                ctx.keep_inscope_tys(t, self).ok()?;
                if t.len() == 1 {
                    Some(t[0])
                } else {
                    None
                }
            }
        }
    }

    fn get_tmp_variable(&mut self, name: &str, ctx: ContextNode) -> Option<ContextVarNode> {
        let cvar = ctx.tmp_var_by_name(self, name)?;
        Some(cvar.latest_version_or_inherited_in_ctx(ctx, self))
    }

    fn get_unchanged_tmp_variable(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        name: &str,
        ctx: ContextNode,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        let Some(var) = self.get_tmp_variable(name, ctx) else {
            return Ok(None);
        };

        if let Some(tmp) = var.tmp_of(self)? {
            if tmp.lhs.latest_version_or_inherited_in_ctx(ctx, self) != tmp.lhs {
                let latest = tmp.lhs.latest_version_or_inherited_in_ctx(ctx, self);
                let newest_min = latest.evaled_range_min(self, arena)?;
                let curr_min = tmp.lhs.evaled_range_min(self, arena)?;
                if newest_min != curr_min {
                    return Ok(None);
                }
                let newest_max = latest.evaled_range_max(self, arena)?;
                let curr_max = tmp.lhs.evaled_range_max(self, arena)?;
                if newest_max != curr_max {
                    return Ok(None);
                }
            }

            if let Some(rhs) = tmp.rhs {
                if rhs.latest_version_or_inherited_in_ctx(ctx, self) != rhs {
                    let latest = rhs.latest_version_or_inherited_in_ctx(ctx, self);
                    let newest_min = latest.evaled_range_min(self, arena)?;
                    let curr_min = rhs.evaled_range_min(self, arena)?;
                    if newest_min != curr_min {
                        return Ok(None);
                    }
                    let newest_max = latest.evaled_range_max(self, arena)?;
                    let curr_max = rhs.evaled_range_max(self, arena)?;
                    if newest_max != curr_max {
                        return Ok(None);
                    }
                }
            }

            Ok(Some(var))
        } else {
            Ok(Some(var))
        }
    }

    /// Match on the [`ExprRet`]s of a variable definition and construct the variable
    fn match_var_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        (name, storage): (
            Option<impl ToString + Clone>,
            Option<shared::StorageLocation>,
        ),
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
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                let res = rhs_cvar.literal_cast_from_ty(ty, self).into_expr_err(loc);
                let _ = self.add_if_err(res);
                self.match_var_def(
                    arena,
                    ctx,
                    (name, storage),
                    loc,
                    lhs_paths,
                    Some(&ExprRet::Single(rhs_cvar.into())),
                )
            }
            (ExprRet::Single(ty), Some(ExprRet::Single(rhs))) => {
                let name = name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage,
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    dep_on: None,
                    is_return: false,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(var));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));

                if let Some(strukt) = lhs.ty(self).into_expr_err(loc)?.maybe_struct() {
                    strukt
                        .add_fields_to_cvar(self, loc, lhs)
                        .into_expr_err(loc)?;
                }
                let rhs = ContextVarNode::from(*rhs);

                self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                    let _ = analyzer.assign(arena, loc, lhs, rhs, ctx)?;
                    // match_assign_ret(analyzer, ctx, ret);
                    Ok(())
                })?;

                Ok(false)
            }
            (ExprRet::Single(ty), None) => {
                let name = name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let maybe_struct = ty.maybe_struct();
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: storage.as_ref().copied(),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    dep_on: None,
                    is_return: false,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(var));
                ctx.add_var(lhs, self).into_expr_err(loc)?;
                self.add_edge(lhs, ctx, Edge::Context(ContextEdge::Variable));
                if let Some(strukt) = maybe_struct {
                    strukt
                        .add_fields_to_cvar(self, loc, lhs)
                        .into_expr_err(loc)?;
                }
                Ok(false)
            }
            (l @ ExprRet::Single(_lhs), Some(ExprRet::Multi(rhs_sides))) => Ok(rhs_sides
                .iter()
                .map(|expr_ret| {
                    self.match_var_def(arena, ctx, (name.clone(), storage), loc, l, Some(expr_ret))
                })
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), r @ Some(ExprRet::Single(_))) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| {
                    self.match_var_def(arena, ctx, (name.clone(), storage), loc, expr_ret, r)
                })
                .collect::<Result<Vec<_>, ExprErr>>()?
                .iter()
                .all(|e| *e)),
            (ExprRet::Multi(lhs_sides), None) => Ok(lhs_sides
                .iter()
                .map(|expr_ret| {
                    self.match_var_def(arena, ctx, (name.clone(), storage), loc, expr_ret, None)
                })
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
                            self.match_var_def(
                                arena,
                                ctx,
                                (name.clone(), storage),
                                loc,
                                lhs_expr_ret,
                                Some(rhs_expr_ret),
                            )
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                } else {
                    Ok(rhs_sides
                        .iter()
                        .map(|rhs_expr_ret| {
                            self.match_var_def(
                                arena,
                                ctx,
                                (name.clone(), storage),
                                loc,
                                lhs_paths,
                                Some(rhs_expr_ret),
                            )
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?
                        .iter()
                        .all(|e| *e))
                }
            }
            (_, _) => Err(ExprErr::Todo(
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

        let maybe_old_ctx = cvar_node.maybe_ctx(self);
        if maybe_old_ctx.is_some() && maybe_old_ctx != Some(ctx) {
            if let Some(cvar) = cvar_node.next_version_or_inherited_in_ctx(ctx, self) {
                panic!(
                    "Not latest version of (inherited): {}, old context: {}, new context: {}",
                    cvar.display_name(self).unwrap(),
                    maybe_old_ctx.unwrap().path(self),
                    ctx.path(self),
                );
            }
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
            .latest_version_or_inherited_in_ctx(ctx, self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
        // get the old context
        let new_cvarnode;

        'a: {
            if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
                if !force {
                    // get the previous version to remove and prevent spurious nodes
                    if let Some(prev) = cvar_node
                        .latest_version_or_inherited_in_ctx(ctx, self)
                        .previous_version(self)
                    {
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
                new_cvarnode = self.add_node(new_cvar);
                if old_ctx != ctx {
                    tracing::trace!(
                        "moving var {} into new context: from {} to {}",
                        ContextVarNode::from(new_cvarnode)
                            .display_name(self)
                            .unwrap(),
                        old_ctx.path(self),
                        ctx.path(self),
                    );
                    ctx.add_var(new_cvarnode.into(), self).into_expr_err(loc)?;
                    self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(
                        new_cvarnode,
                        cvar_node.0,
                        Edge::Context(ContextEdge::InheritedVariable),
                    );

                    let from_fields = cvar_node.struct_to_fields(self).into_expr_err(loc)?;
                    let mut struct_stack = from_fields
                        .into_iter()
                        .map(|i| (i, new_cvarnode))
                        .collect::<Vec<_>>();
                    while let Some((field, parent)) = struct_stack.pop() {
                        let underlying = field.underlying(self).into_expr_err(loc)?;
                        let new_field_in_inheritor = self.add_node(underlying.clone());
                        self.add_edge(
                            new_field_in_inheritor,
                            parent,
                            Edge::Context(ContextEdge::AttrAccess("field")),
                        );

                        let sub_fields = field.struct_to_fields(self).into_expr_err(loc)?;
                        struct_stack.extend(
                            sub_fields
                                .into_iter()
                                .map(|i| (i, new_field_in_inheritor))
                                .collect::<Vec<_>>(),
                        );
                    }
                } else {
                    self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
                }
            } else {
                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(new_cvar);
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        }

        self.mark_dirty(new_cvarnode);

        Ok(ContextVarNode::from(new_cvarnode))
    }

    fn advance_var_in_forced_ctx(
        &mut self,
        mut cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<ContextVarNode, ExprErr> {
        if cvar_node.maybe_ctx(self) != Some(ctx) {
            if let Some(inherited) = cvar_node
                .latest_version_or_inherited_in_ctx(ctx, self)
                .next_version_or_inherited_in_ctx(ctx, self)
            {
                cvar_node = inherited.latest_version_or_inherited_in_ctx(ctx, self)
            }
        }

        let mut new_cvar = cvar_node
            .latest_version_or_inherited_in_ctx(ctx, self)
            .underlying(self)
            .into_expr_err(loc)?
            .clone();
        // get the old context
        let new_cvarnode;

        'a: {
            if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
                // get the previous version to remove and prevent spurious nodes
                if let Some(prev) = cvar_node
                    .latest_version_or_inherited_in_ctx(ctx, self)
                    .previous_version(self)
                {
                    let prev_version = prev.underlying(self).into_expr_err(loc)?;
                    // check if there was no change between the previous version and the latest version
                    if prev_version.eq_ignore_loc(&new_cvar) && old_ctx == ctx {
                        // there was no change in the current context, just give them the current variable
                        new_cvarnode = cvar_node.into();
                        break 'a;
                    }
                }

                new_cvar.loc = Some(loc);
                // new_cvar.display_name = format!("{}_{}", new_cvar.name, cvar_node.prev_versions(self));
                new_cvarnode = self.add_node(new_cvar);
                if old_ctx != ctx {
                    tracing::trace!(
                        "moving var {} into new context: from {} to {}",
                        ContextVarNode::from(new_cvarnode)
                            .display_name(self)
                            .unwrap(),
                        old_ctx.path(self),
                        ctx.path(self),
                    );
                    ctx.add_var(new_cvarnode.into(), self).into_expr_err(loc)?;
                    self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(
                        new_cvarnode,
                        cvar_node.0,
                        Edge::Context(ContextEdge::InheritedVariable),
                    );

                    let from_fields = cvar_node.struct_to_fields(self).into_expr_err(loc)?;
                    let mut struct_stack = from_fields
                        .into_iter()
                        .map(|i| (i, new_cvarnode))
                        .collect::<Vec<_>>();
                    while let Some((field, parent)) = struct_stack.pop() {
                        let underlying = field.underlying(self).into_expr_err(loc)?;
                        let new_field_in_inheritor = self.add_node(underlying.clone());
                        self.add_edge(
                            new_field_in_inheritor,
                            parent,
                            Edge::Context(ContextEdge::AttrAccess("field")),
                        );

                        let sub_fields = field.struct_to_fields(self).into_expr_err(loc)?;
                        struct_stack.extend(
                            sub_fields
                                .into_iter()
                                .map(|i| (i, new_field_in_inheritor))
                                .collect::<Vec<_>>(),
                        );
                    }
                } else {
                    self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
                }
            } else {
                new_cvar.loc = Some(loc);
                new_cvarnode = self.add_node(new_cvar);
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        }

        self.mark_dirty(new_cvarnode);

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
        let new_cvarnode = self.add_node(new_cvar);
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode)
            .underlying_mut(self)
            .unwrap()
    }
}
