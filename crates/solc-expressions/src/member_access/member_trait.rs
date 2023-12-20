use graph::nodes::ConcreteNode;
use graph::nodes::Concrete;
use crate::{
    BuiltinAccess, ContextBuilder, ContractAccess, EnumAccess, Env, ExprErr, ExpressionParser,
    IntoExprErr, ListAccess, StructAccess,
};

use graph::{
    nodes::{
        BuiltInNode, ContextNode, ContextVar, ContextVarNode, ContractNode, EnumNode, ExprRet,
        FunctionNode, StructNode, TyNode,
    },
    AnalyzerBackend, Node, TypeNode, VarType,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Identifier, Loc};

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
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        // TODO: this is wrong as it overwrites a function call of the form elem.length(...) i believe
        if ident.name == "length" {
            return self.length(loc, member_expr, ctx);
        }

        self.parse_ctx_expr(member_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(
                    loc,
                    "Attempted to perform member access without a left-hand side".to_string(),
                ));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_member(ctx, loc, ident, ret)
        })
    }

    /// Match on [`ExprRet`]s and call the member access for each
    fn match_member(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        ident: &Identifier,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(idx) | ExprRet::SingleLiteral(idx) => {
                ctx.push_expr(self.member_access_inner(loc, idx, ident, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Multi(inner) => inner
                .into_iter()
                .try_for_each(|ret| self.match_member(ctx, loc, ident, ret)),
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Null => Ok(()),
        }
    }

    /// Perform the member access
    fn member_access_inner(
        &mut self,
        loc: Loc,
        member_idx: NodeIdx,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        match self.node(member_idx) {
            Node::ContextVar(cvar) => {
                self.member_access_var_ty(cvar.clone(), loc, member_idx, ident, ctx)
            }
            Node::Contract(_c) => self.contract_member_access(
                member_idx,
                ContractNode::from(member_idx),
                ident,
                ctx,
                loc,
                None,
            ),
            Node::Struct(_c) => self.struct_member_access(
                member_idx,
                StructNode::from(member_idx),
                ident,
                ctx,
                loc,
                None,
            ),
            Node::Enum(_c) => {
                self.enum_member_access(member_idx, EnumNode::from(member_idx), ident, ctx, loc)
            }
            Node::Ty(_ty) => {
                self.ty_member_access(member_idx, TyNode::from(member_idx), ident, ctx, loc, None)
            }
            Node::Msg(_msg) => self.msg_access(loc, ctx, &ident.name),
            Node::Block(_b) => self.block_access(loc, ctx, &ident.name),
            Node::Builtin(ref _b) => {
                self.builtin_member_access(loc, ctx, BuiltInNode::from(member_idx), false, ident)
            }
            e => Err(ExprErr::Todo(
                loc,
                format!("Member access on type: {e:?} is not yet supported"),
            )),
        }
    }

    /// Get visible functions for this member
    fn visible_member_funcs(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_idx: NodeIdx,
    ) -> Result<Vec<FunctionNode>, ExprErr> {
        let res = match self.node(member_idx) {
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Contract(con_node), _) => {
                    let cnode = *con_node;
                    let mut funcs = cnode.linearized_functions(self).into_expr_err(loc)?;
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
                VarType::User(TypeNode::Func(func_node), _) => self
                    .possible_library_funcs(ctx, func_node.0.into())
                    .into_iter()
                    .collect::<Vec<_>>(),
                VarType::User(TypeNode::Unresolved(n), _) => {
                    match self.node(*n) {
                        Node::Unresolved(ident) => {
                            return Err(ExprErr::Unresolved(loc, format!("The type \"{}\" is currently unresolved but should have been resolved by now. This is a bug.", ident.name)))
                        }
                        _ => unreachable!()
                    }
                }
            },
            Node::Contract(_) => ContractNode::from(member_idx).funcs(self),
            Node::Concrete(_)
            | Node::Ty(_)
            | Node::Struct(_)
            | Node::Function(_)
            | Node::Enum(_)
            | Node::Builtin(_) => self
                .possible_library_funcs(ctx, member_idx)
                .into_iter()
                .collect::<Vec<_>>(),
            e => {
                return Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("This type cannot have member functions: {:?}", e),
                ))
            }
        };
        Ok(res)
    }

    /// Perform member access for a variable type
    fn member_access_var_ty(
        &mut self,
        cvar: ContextVar,
        loc: Loc,
        member_idx: NodeIdx,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        match &cvar.ty {
            VarType::User(TypeNode::Struct(struct_node), _) => {
                self.struct_member_access(member_idx, *struct_node, ident, ctx, loc, Some(cvar))
            }
            VarType::User(TypeNode::Enum(enum_node), _) => {
                self.enum_member_access(member_idx, *enum_node, ident, ctx, loc)
            }
            VarType::User(TypeNode::Func(func_node), _) => {
                self.func_member_access(*func_node, ident, ctx, loc)
            }
            VarType::User(TypeNode::Ty(ty_node), _) => {
                self.ty_member_access(member_idx, *ty_node, ident, ctx, loc, Some(cvar))
            }
            VarType::User(TypeNode::Contract(con_node), _) => {
                self.contract_member_access(member_idx, *con_node, ident, ctx, loc, Some(cvar))
            }
            VarType::BuiltIn(bn, _) => self.builtin_member_access(
                loc,
                ctx,
                *bn,
                ContextVarNode::from(member_idx)
                    .is_storage(self)
                    .into_expr_err(loc)?,
                ident,
            ),
            VarType::Concrete(cn) => {
                let builtin = cn.underlying(self).into_expr_err(loc)?.as_builtin();
                let bn = self.builtin_or_add(builtin).into();
                self.builtin_member_access(
                    loc,
                    ctx,
                    bn,
                    ContextVarNode::from(member_idx)
                        .is_storage(self)
                        .into_expr_err(loc)?,
                    ident,
                )
            }
            e => Err(ExprErr::UnhandledCombo(
                loc,
                format!("Unhandled member access: {:?}, {:?}", e, ident),
            )),
        }
    }

    /// Perform a `TyNode` member access
    fn ty_member_access(
        &mut self,
        _member_idx: NodeIdx,
        ty_node: TyNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
        _maybe_parent: Option<ContextVar>,
    ) -> Result<ExprRet, ExprErr> {
        let name = ident.name.split('(').collect::<Vec<_>>()[0];
        if let Some(func) = self.library_func_search(ctx, ty_node.0.into(), ident) {
            Ok(func)
        } else if let Some(func) = self.builtin_fn_or_maybe_add(name) {
            Ok(ExprRet::Single(func))
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on struct \"{}\"",
                    ident.name,
                    ty_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }

    /// Access function members
    fn func_member_access(
        &mut self,
        func_node: FunctionNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        let prefix_only_name = func_node
            .prefix_only_name(self)
            .into_expr_err(loc)?
            .unwrap();
        let name = format!("{}.{}", prefix_only_name, ident.name);
        tracing::trace!("Function member access: {}", name);
        match &*ident.name {
            "selector" => {
                let mut out = [0; 32];
                keccak_hash::keccak_256(prefix_only_name.as_bytes(), &mut out);
                let selector: [u8; 4] = [out[0], out[1], out[2], out[3]];
                let selector_conc = Node::Concrete(Concrete::from(selector));
                let selector_node = ConcreteNode::from(self.add_node(selector_conc));
                let var = ContextVar::new_from_concrete(loc, ctx, selector_node, self)
                    .into_expr_err(loc)?;
                let cvar = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single(cvar))
            }
            _ => Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on function \"{}\"",
                    ident.name, prefix_only_name
                ),
            )),
        }
    }
}
