use crate::{
    BuiltinAccess, ContractAccess, EnumAccess, Env, ErrorAccess, ListAccess, StructAccess,
};
use graph::ContextEdge;
use graph::Edge;

use graph::{
    elem::Elem,
    nodes::{
        BuiltInNode, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode, ContractNode,
        EnumNode, EnvCtxNode, ExprRet, FunctionNode, StructNode, TyNode,
    },
    AnalyzerBackend, Node, TypeNode, VarType,
};
use shared::GraphError;
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> MemberAccessParts for T where
    T: BuiltinAccess + ContractAccess + EnumAccess + ListAccess + StructAccess
{
}

/// Supertrait that coalesces various member access traits
pub trait MemberAccessParts:
    BuiltinAccess + ContractAccess + EnumAccess + ListAccess + StructAccess
{
}

impl<T> MemberAccess for T where
    T: MemberAccessParts + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}

/// Toplevel trait for performing member access. Utilizes other `..Access` traits
pub trait MemberAccess:
    MemberAccessParts + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Entry function for perform a member access
    #[tracing::instrument(level = "trace", skip_all)]
    fn member_access(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        member: ExprRet,
        name: &str,
        loc: Loc,
    ) -> Result<bool, ExprErr> {
        // TODO: this is wrong as it overwrites a function call of the form elem.length(...) i believe
        if name == "length" {
            self.length(arena, ctx, member, loc)?;
            return Ok(false);
        }

        self.match_member(ctx, member, name, loc)
    }

    /// Match on [`ExprRet`]s and call the member access for each
    fn match_member(
        &mut self,
        ctx: ContextNode,
        member: ExprRet,
        name: &str,
        loc: Loc,
    ) -> Result<bool, ExprErr> {
        match member {
            ExprRet::Single(idx) | ExprRet::SingleLiteral(idx) => {
                let (inner, was_lib_func) = self.member_access_inner(ctx, idx, name, loc)?;
                ctx.push_expr(inner, self).into_expr_err(loc)?;
                Ok(was_lib_func)
            }
            ExprRet::Multi(inner) => {
                inner.into_iter().try_for_each(|member| {
                    let _ = self.match_member(ctx, member, name, loc)?;
                    Ok(())
                })?;
                Ok(false)
            }
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)?;
                Ok(false)
            }
            ExprRet::Null => Ok(false),
        }
    }

    /// Perform the member access
    #[tracing::instrument(level = "trace", skip_all)]
    fn member_access_inner(
        &mut self,
        ctx: ContextNode,
        member_idx: NodeIdx,
        name: &str,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        match self.node(member_idx) {
            Node::ContextVar(_) => {
                self.member_access_var(ctx, ContextVarNode::from(member_idx), name, loc)
            }
            Node::Contract(_c) => {
                self.contract_member_access(ctx, None, ContractNode::from(member_idx), name, loc)
            }
            Node::Struct(_c) => {
                let var =
                    self.add_node(ContextVar::maybe_from_user_ty(self, loc, member_idx).unwrap());
                self.struct_var_member_access(
                    ctx,
                    var.into(),
                    StructNode::from(member_idx),
                    name,
                    loc,
                )
            }
            Node::Enum(_c) => self.enum_member_access(ctx, EnumNode::from(member_idx), name, loc),
            Node::Ty(_ty) => self.ty_member_access(ctx, TyNode::from(member_idx), name, loc),
            Node::Msg(_msg) => {
                let res = self.msg_access(ctx, name, loc)?;
                Ok((res, false))
            }
            Node::Block(_b) => {
                let res = self.block_access(ctx, name, loc)?;
                Ok((res, false))
            }
            Node::Builtin(ref _b) => {
                self.builtin_member_access(ctx, BuiltInNode::from(member_idx), name, false, loc)
            }
            Node::EnvCtx(_) => {
                if let Some(var) = EnvCtxNode::from(member_idx)
                    .member_access(self, name)
                    .into_expr_err(loc)?
                {
                    let full_name = var.name(self).unwrap();
                    if let Some(prev_defined) = ctx
                        .var_by_name_or_recurse(self, &full_name)
                        .into_expr_err(loc)?
                    {
                        Ok((
                            ExprRet::Single(prev_defined.latest_version(self).0.into()),
                            false,
                        ))
                    } else {
                        let cloned = var.latest_version(self).underlying(self).unwrap().clone();
                        let new_var = self.add_node(cloned);
                        ctx.add_var(new_var.into(), self).into_expr_err(loc)?;
                        self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
                        let e_mut = EnvCtxNode::from(member_idx).underlying_mut(self).unwrap();
                        e_mut.set(name, new_var);
                        Ok((ExprRet::Single(new_var), false))
                    }
                } else {
                    let msg_access = self.msg_access(ctx, name, loc)?;
                    let access = msg_access.expect_single().into_expr_err(loc)?;
                    ctx.add_var(access.into(), self).into_expr_err(loc)?;
                    self.add_edge(access, ctx, Edge::Context(ContextEdge::Variable));
                    let e_mut = EnvCtxNode::from(member_idx).underlying_mut(self).unwrap();
                    e_mut.set(name, access);
                    Ok((msg_access, false))
                }
            }
            e => Err(ExprErr::Todo(
                loc,
                format!("Member access on type: {e:?} is not yet supported"),
            )),
        }
    }

    /// Get visible functions for this member
    #[tracing::instrument(level = "trace", skip_all)]
    fn visible_member_funcs(
        &mut self,
        ctx: ContextNode,
        member_idx: NodeIdx,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        let res = match self.node(member_idx) {
            Node::ContextVar(cvar) => {
                tracing::trace!(
                    "looking for visible member functions of type: {:?}",
                    cvar.ty
                );
                match &cvar.ty {
                    VarType::User(TypeNode::Contract(con_node), _) => {
                        let cnode = *con_node;
                        let mut funcs = cnode.linearized_functions(self, false)?;
                        self
                        .possible_library_funcs(ctx, cnode.0.into())
                        .into_iter()
                        .for_each(|func| {
                            let name = func.name(self).unwrap();
                            funcs.entry(name).or_insert(func);
                        });
                        funcs.values().copied().collect()
                    },
                    VarType::BuiltIn(bn, _) => self
                        .possible_library_funcs(ctx, bn.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::Concrete(cnode) => {
                        let b = cnode.underlying(self).unwrap().as_builtin();
                        let bn = self.builtin_or_add(b);
                        self.possible_library_funcs(ctx, bn)
                            .into_iter()
                            .collect::<Vec<_>>()
                    }
                    VarType::User(TypeNode::Struct(sn), _) => self
                        .possible_library_funcs(ctx, sn.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::User(TypeNode::Enum(en), _) => self
                        .possible_library_funcs(ctx, en.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::User(TypeNode::Ty(ty), _) => self
                        .possible_library_funcs(ctx, ty.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::User(TypeNode::Error(err), _) => self
                        .possible_library_funcs(ctx, err.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::User(TypeNode::Func(func_node), _) => self
                        .possible_library_funcs(ctx, func_node.0.into())
                        .into_iter()
                        .collect::<Vec<_>>(),
                    VarType::User(TypeNode::Unresolved(n), _) => {
                        match self.node(*n) {
                            Node::Unresolved(ident) => {
                                return Err(GraphError::UnknownVariable(format!("The type \"{}\" is currently unresolved but should have been resolved by now. This is a bug.", ident.name)))
                            }
                            _ => unreachable!()
                        }
                    }
                }
            }
            Node::Contract(_) => ContractNode::from(member_idx).funcs(self),
            Node::Concrete(_) => {
                let b = ConcreteNode::from(member_idx)
                    .underlying(self)
                    .unwrap()
                    .as_builtin();
                let bn = self.builtin_or_add(b);
                self.possible_library_funcs(ctx, bn)
                    .into_iter()
                    .collect::<Vec<_>>()
            }
            Node::Ty(_)
            | Node::Struct(_)
            | Node::Function(_)
            | Node::Enum(_)
            | Node::Builtin(_) => self
                .possible_library_funcs(ctx, member_idx)
                .into_iter()
                .collect::<Vec<_>>(),
            e => {
                return Err(GraphError::NodeConfusion(format!(
                    "This type cannot have member functions: {:?}",
                    e
                )))
            }
        };
        Ok(res)
    }

    /// Perform member access for a variable type
    #[tracing::instrument(level = "trace", skip_all)]
    fn member_access_var(
        &mut self,
        ctx: ContextNode,
        cvar: ContextVarNode,
        name: &str,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        match cvar.ty(self).into_expr_err(loc)? {
            VarType::User(TypeNode::Struct(struct_node), _) => {
                self.struct_var_member_access(ctx, cvar, *struct_node, name, loc)
            }
            VarType::User(TypeNode::Error(err_node), _) => {
                self.error_var_member_access(ctx, cvar, *err_node, name, loc)
            }
            VarType::User(TypeNode::Enum(enum_node), _) => {
                self.enum_member_access(ctx, *enum_node, name, loc)
            }
            VarType::User(TypeNode::Func(func_node), _) => {
                Ok((self.func_member_access(ctx, *func_node, name, loc)?, false))
            }
            VarType::User(TypeNode::Ty(ty_node), _) => {
                self.ty_member_access(ctx, *ty_node, name, loc)
            }
            VarType::User(TypeNode::Contract(con_node), _) => {
                self.contract_member_access(ctx, Some(cvar), *con_node, name, loc)
            }
            VarType::BuiltIn(bn, _) => self.builtin_member_access(
                ctx,
                *bn,
                name,
                cvar.is_storage(self).into_expr_err(loc)?,
                loc,
            ),
            VarType::Concrete(cn) => {
                let builtin = cn.underlying(self).into_expr_err(loc)?.as_builtin();
                let bn = self.builtin_or_add(builtin).into();
                self.builtin_member_access(
                    ctx,
                    bn,
                    name,
                    cvar.is_storage(self).into_expr_err(loc)?,
                    loc,
                )
            }
            e => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled member access: {:?}, {:?}", e, name),
            )),
        }
    }

    /// Perform a `TyNode` member access
    #[tracing::instrument(level = "trace", skip_all)]
    fn ty_member_access(
        &mut self,
        ctx: ContextNode,
        ty_node: TyNode,
        name: &str,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        let name = name.split('(').collect::<Vec<_>>()[0];
        if let Some(func) = self.library_func_search(ctx, ty_node.0.into(), name) {
            Ok((func, true))
        } else if let Some(func) = self.builtin_fn_or_maybe_add(name) {
            Ok((ExprRet::Single(func), false))
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{name}\" on struct \"{}\"",
                    ty_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }

    /// Access function members
    #[tracing::instrument(level = "trace", skip_all)]
    fn func_member_access(
        &mut self,
        ctx: ContextNode,
        func_node: FunctionNode,
        name: &str,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        let prefix_only_name = func_node
            .prefix_only_name(self)
            .into_expr_err(loc)?
            .unwrap();
        let func_mem_name = format!("{}.{}", prefix_only_name, name);
        tracing::trace!("Function member access: {}", func_mem_name);
        match &*func_mem_name {
            "selector" => {
                let mut out = [0; 32];
                keccak_hash::keccak_256(prefix_only_name.as_bytes(), &mut out);
                let selector: [u8; 4] = [out[0], out[1], out[2], out[3]];
                let selector_conc = Node::Concrete(Concrete::from(selector));
                let selector_node = ConcreteNode::from(self.add_node(selector_conc));
                let var = ContextVar::new_from_concrete(loc, ctx, selector_node, self)
                    .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                Ok(ExprRet::Single(cvar))
            }
            _ => Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{name}\" on function \"{}\"",
                    prefix_only_name
                ),
            )),
        }
    }
}
