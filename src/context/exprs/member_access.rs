use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{context::exprs::variable::Variable, ContextBuilder, NodeIdx};
use petgraph::{visit::EdgeRef, Direction};
use shared::range::elem_ty::Elem;
use shared::range::Range;
use shared::{
    analyzer::AnalyzerLike,
    context::*,
    nodes::*,
    range::SolcRange,
    {Edge, Node},
};
use std::collections::BTreeSet;

use ethers_core::types::{I256, U256};

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> MemberAccess for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait MemberAccess: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn visible_member_funcs(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_idx: NodeIdx,
    ) -> Result<Vec<FunctionNode>, ExprErr> {
        let res = match self.node(member_idx) {
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Contract(con_node), _) => {
                    let mut funcs = con_node.linearized_functions(self);
                    self
                    .possible_library_funcs(ctx, con_node.0.into())
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

    /// Gets the array type
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
                return Err(ExprErr::NoLhs(loc, "Attempted to perform member access without a left-hand side".to_string()));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_member(ctx, loc, ident, ret)
        })
    }

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

    fn struct_member_access(
        &mut self,
        member_idx: NodeIdx,
        struct_node: StructNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
        maybe_parent: Option<ContextVar>,
    ) -> Result<ExprRet, ExprErr> {
        let name = format!(
            "{}.{}",
            struct_node.name(self).into_expr_err(loc)?,
            ident.name
        );
        tracing::trace!("Struct member access: {}", name);
        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            Ok(ExprRet::Single(attr_var.latest_version(self).into()))
        } else if let Some(field) = struct_node.find_field(self, ident) {
            let cvar = if let Some(parent) = maybe_parent {
                parent
            } else {
                ContextVar::maybe_from_user_ty(self, loc, struct_node.into()).unwrap()
            };
            if let Some(field_cvar) = ContextVar::maybe_new_from_field(
                self,
                loc,
                &cvar,
                field.underlying(self).unwrap().clone(),
            ) {
                let fc_node = self.add_node(Node::ContextVar(field_cvar));
                self.add_edge(
                    fc_node,
                    ContextVarNode::from(member_idx).first_version(self),
                    Edge::Context(ContextEdge::AttrAccess),
                );
                ctx.add_var(fc_node.into(), self).into_expr_err(loc)?;
                self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                Ok(ExprRet::Single(fc_node))
            } else {
                panic!("Couldn't create field variable");
            }
        } else if let Some(func) = self.library_func_search(ctx, struct_node.0.into(), ident) {
            Ok(func)
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on struct \"{}\"",
                    ident.name,
                    struct_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }

    fn enum_member_access(
        &mut self,
        _member_idx: NodeIdx,
        enum_node: EnumNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!("Enum member access: {}", ident.name);

        if let Some(variant) = enum_node
            .variants(self)
            .into_expr_err(loc)?
            .iter()
            .find(|variant| **variant == ident.name)
        {
            let var =
                ContextVar::new_from_enum_variant(self, ctx, loc, enum_node, variant.to_string())
                    .into_expr_err(loc)?;
            let cvar = self.add_node(Node::ContextVar(var));
            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
            Ok(ExprRet::Single(cvar))
        } else if let Some(ret) = self.library_func_search(ctx, enum_node.0.into(), ident) {
            Ok(ret)
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on enum \"{}\"",
                    ident.name,
                    enum_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }

    fn contract_member_access(
        &mut self,
        member_idx: NodeIdx,
        con_node: ContractNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
        maybe_parent: Option<ContextVar>,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "Contract member access: {}.{}",
            con_node
                .maybe_name(self)
                .into_expr_err(loc)?
                .unwrap_or_else(|| "interface".to_string()),
            ident.name
        );

        if let Some(func) = con_node
            .funcs(self)
            .into_iter()
            .find(|func_node| func_node.name(self).unwrap() == ident.name)
        {
            if let Some(func_cvar) = ContextVar::maybe_from_user_ty(self, loc, func.0.into()) {
                let fn_node = self.add_node(Node::ContextVar(func_cvar));
                // this prevents attaching a dummy node to the parent which could cause a cycle in the graph
                if maybe_parent.is_some() {
                    self.add_edge(fn_node, member_idx, Edge::Context(ContextEdge::FuncAccess));
                }
                Ok(ExprRet::Single(fn_node))
            } else {
                Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unable to construct the function \"{}\" in contract \"{}\"",
                        ident.name,
                        con_node.name(self).into_expr_err(loc)?
                    ),
                ))
            }
        } else if let Some(func) = con_node
            .structs(self)
            .into_iter()
            .find(|struct_node| struct_node.name(self).unwrap() == ident.name)
        {
            if let Some(struct_cvar) = ContextVar::maybe_from_user_ty(self, loc, func.0.into()) {
                let struct_node = self.add_node(Node::ContextVar(struct_cvar));
                // this prevents attaching a dummy node to the parent which could cause a cycle in the graph
                if maybe_parent.is_some() {
                    self.add_edge(
                        struct_node,
                        member_idx,
                        Edge::Context(ContextEdge::StructAccess),
                    );
                }
                return Ok(ExprRet::Single(struct_node));
            } else {
                return Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unable to construct the struct \"{}\" in contract \"{}\"",
                        ident.name,
                        con_node.name(self).into_expr_err(loc)?
                    ),
                ));
            }
        } else {
            match &*ident.name {
                "name" => {
                    let c = Concrete::from(con_node.name(self).unwrap());
                    let cnode = self.add_node(Node::Concrete(c));
                    let cvar = ContextVar::new_from_concrete(loc, ctx, cnode.into(), self)
                        .into_expr_err(loc)?;
                    let node = self.add_node(Node::ContextVar(cvar));
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    return Ok(ExprRet::Single(node));
                }
                "creationCode" | "runtimeCode" => {
                    let bn = self.builtin_or_add(Builtin::DynamicBytes);
                    let cvar =
                        ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(Node::ContextVar(cvar));
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    return Ok(ExprRet::Single(node));
                }
                "interfaceId" => {
                    // TODO: actually calculate this
                    let bn = self.builtin_or_add(Builtin::Bytes(4));
                    let cvar =
                        ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(Node::ContextVar(cvar));
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    return Ok(ExprRet::Single(node));
                }
                _ => {
                    return Err(ExprErr::ContractFunctionNotFound(
                        loc,
                        format!(
                        "No function or struct with name {:?} in contract: {:?}. Functions: {:#?}",
                        ident.name,
                        con_node.name(self).unwrap(),
                        con_node
                            .funcs(self)
                            .iter()
                            .map(|func| func.name(self).unwrap())
                            .collect::<Vec<_>>()
                    ),
                    ))
                }
            }
        }
    }

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
            Node::Msg(_msg) => {
                let name = format!("msg.{}", ident.name);
                tracing::trace!("Msg Env member access: {}", name);

                if let Some(attr_var) =
                    ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)?
                {
                    Ok(ExprRet::Single(attr_var.latest_version(self).into()))
                } else {
                    let (node, name) = match &*ident.name {
                        "data" => {
                            if let Some(d) =
                                self.msg().underlying(self).into_expr_err(loc)?.data.clone()
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.data".to_string(),
                                )
                            } else {
                                let b = Builtin::DynamicBytes;
                                let node = self.builtin_or_add(b);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "msg.data".to_string();
                                var.display_name = "msg.data".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "sender" => {
                            if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.sender
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.sender".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "msg.sender".to_string();
                                var.display_name = "msg.sender".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "sig" => {
                            if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.sig {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.sig".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Bytes(4));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "msg.sig".to_string();
                                var.display_name = "msg.sig".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "value" => {
                            if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.value {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "msg.value".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "msg.value".to_string();
                                var.display_name = "msg.value".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "origin" => {
                            if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.origin
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "tx.origin".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "tx.origin".to_string();
                                var.display_name = "tx.origin".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "gasprice" => {
                            if let Some(d) =
                                self.msg().underlying(self).into_expr_err(loc)?.gasprice
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "tx.gasprice".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(64));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "tx.gasprice".to_string();
                                var.display_name = "tx.gasprice".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "gaslimit" => {
                            if let Some(d) =
                                self.msg().underlying(self).into_expr_err(loc)?.gaslimit
                            {
                                let c = Concrete::from(d);
                                (self.add_node(Node::Concrete(c)).into(), "".to_string())
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(64));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        e => {
                            return Err(ExprErr::MemberAccessNotFound(
                                loc,
                                format!("Unknown member access on msg: {e:?}"),
                            ))
                        }
                    };

                    let mut var =
                        ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(cvar))
                }
            }
            Node::Block(_b) => {
                let name = format!("block.{}", ident.name);
                tracing::trace!("Block Env member access: {}", name);
                if let Some(attr_var) =
                    ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)?
                {
                    Ok(ExprRet::Single(attr_var.latest_version(self).into()))
                } else {
                    let (node, name) = match &*ident.name {
                        "hash" => {
                            if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.hash
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.blockhash".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Bytes(32));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.blockhash".to_string();
                                var.display_name = "block.blockhash".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "basefee" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.basefee
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.basefee".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.basefee".to_string();
                                var.display_name = "block.basefee".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "chainid" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.chainid
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.chainid".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.chainid".to_string();
                                var.display_name = "block.chainid".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "coinbase" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.coinbase
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.coinbase".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Address);
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.coinbase".to_string();
                                var.display_name = "block.coinbase".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "difficulty" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.difficulty
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.difficulty".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.difficulty".to_string();
                                var.display_name = "block.difficulty".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "gaslimit" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.gaslimit
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.gaslimit".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.gaslimit".to_string();
                                var.display_name = "block.gaslimit".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "number" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.number
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.number".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.number".to_string();
                                var.display_name = "block.number".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "prevrandao" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.prevrandao
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.prevrandao".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.prevrandao".to_string();
                                var.display_name = "block.prevrandao".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        "timestamp" => {
                            if let Some(d) =
                                self.block().underlying(self).into_expr_err(loc)?.timestamp
                            {
                                let c = Concrete::from(d);
                                (
                                    self.add_node(Node::Concrete(c)).into(),
                                    "block.timestamp".to_string(),
                                )
                            } else {
                                let node = self.builtin_or_add(Builtin::Uint(256));
                                let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                                    .into_expr_err(loc)?;
                                var.name = "block.timestamp".to_string();
                                var.display_name = "block.timestamp".to_string();
                                var.is_tmp = false;
                                var.is_symbolic = true;
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single(cvar));
                            }
                        }
                        e => {
                            return Err(ExprErr::MemberAccessNotFound(
                                loc,
                                format!("Unknown member access on block: {e:?}"),
                            ))
                        }
                    };
                    let mut var =
                        ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(cvar))
                }
            }
            Node::Builtin(ref _b) => {
                self.builtin_member_access(loc, ctx, BuiltInNode::from(member_idx), false, ident)
            }
            e => Err(ExprErr::Todo(
                loc,
                format!("Member access on type: {e:?} is not yet supported"),
            )),
        }
    }

    fn builtin_member_access(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        node: BuiltInNode,
        is_storage: bool,
        ident: &Identifier,
    ) -> Result<ExprRet, ExprErr> {
        if let Some(ret) = self.library_func_search(ctx, node.0.into(), ident) {
            Ok(ret)
        } else {
            match node.underlying(self).into_expr_err(loc)?.clone() {
                Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                    match &*ident.name {
                        "delegatecall"
                        | "call"
                        | "staticcall"
                        | "delegatecall(address, bytes)"
                        | "call(address, bytes)"
                        | "staticcall(address, bytes)" => {
                            // TODO: check if the address is known to be a certain type and the function signature is known
                            // and call into the function
                            let builtin_name = ident.name.split('(').collect::<Vec<_>>()[0];
                            let func_node = self.builtin_fn_or_maybe_add(builtin_name).unwrap();
                            Ok(ExprRet::Single(func_node))
                        }
                        "code" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(node))
                        }
                        "codehash" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Bytes(32));
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(node))
                        }
                        "balance" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Uint(256));
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(node))
                        }
                        _ if ident.name.starts_with("send") => {
                            let bn = self.builtin_or_add(Builtin::Bool);
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(node))
                        }
                        _ if ident.name.starts_with("transfer") => Ok(ExprRet::Multi(vec![])),
                        _ => Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!(
                                "Unknown member access on address: {:?}, ctx: {}",
                                ident.name,
                                ctx.path(self)
                            ),
                        )),
                    }
                }
                Builtin::Bool => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on bool: {:?}, ctx: {}",
                        ident.name,
                        ctx.path(self)
                    ),
                )),
                Builtin::String => match ident.name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let fn_node = self.builtin_fn_or_maybe_add("concat").unwrap();
                        Ok(ExprRet::Single(fn_node))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!(
                            "Unknown member access on string: {:?}, ctx: {}",
                            ident.name,
                            ctx.path(self)
                        ),
                    )),
                },
                Builtin::Bytes(size) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on bytes{}: {:?}", size, ident.name),
                )),
                Builtin::Rational => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on rational: {:?}, ctx: {}",
                        ident.name,
                        ctx.path(self)
                    ),
                )),
                Builtin::DynamicBytes => match ident.name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let fn_node = self.builtin_fn_or_maybe_add("concat").unwrap();
                        Ok(ExprRet::Single(fn_node))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!(
                            "Unknown member access on bytes: {:?}, ctx: {}",
                            ident.name,
                            ctx.path(self)
                        ),
                    )),
                },
                Builtin::Array(_) => {
                    if ident.name.starts_with("push") {
                        if is_storage {
                            let fn_node = self.builtin_fn_or_maybe_add("push").unwrap();
                            Ok(ExprRet::Single(fn_node))
                        } else {
                            Err(ExprErr::NonStoragePush(
                                loc,
                                "Trying to push to nonstorage array is not supported".to_string(),
                            ))
                        }
                    } else if ident.name.starts_with("pop") {
                        if is_storage {
                            let fn_node = self.builtin_fn_or_maybe_add("pop").unwrap();
                            Ok(ExprRet::Single(fn_node))
                        } else {
                            Err(ExprErr::NonStoragePush(
                                loc,
                                "Trying to pop from nonstorage array is not supported".to_string(),
                            ))
                        }
                    } else {
                        Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!(
                                "Unknown member access on array[]: {:?}, ctx: {}",
                                ident.name,
                                ctx.path(self)
                            ),
                        ))
                    }
                }
                Builtin::Mapping(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on mapping: {:?}, ctx: {}",
                        ident.name,
                        ctx.path(self)
                    ),
                )),
                Builtin::Func(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on func: {:?}, ctx: {}",
                        ident.name,
                        ctx.path(self)
                    ),
                )),
                Builtin::Int(size) => {
                    let max = if size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::from(1)
                    };
                    match &*ident.name {
                        "max" => {
                            let c = Concrete::Int(size, max);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.max");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(cvar))
                        }
                        "min" => {
                            let min = max * I256::from(-1i32) - I256::from(1i32);
                            let c = Concrete::Int(size, min);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.min");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(cvar))
                        }
                        e => Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!(
                                "Unknown type attribute on int{size}: {e:?}, ctx: {}",
                                ctx.path(self)
                            ),
                        )),
                    }
                }
                Builtin::Uint(size) => match &*ident.name {
                    "max" => {
                        let size = size;
                        let max = if size == 256 {
                            U256::MAX
                        } else {
                            U256::from(2).pow(U256::from(size)) - 1
                        };
                        let c = Concrete::Uint(size, max);
                        let node = self.add_node(Node::Concrete(c)).into();
                        let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                            .into_expr_err(loc)?;
                        var.name = format!("uint{size}.max");
                        var.display_name = var.name.clone();
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok(ExprRet::Single(cvar))
                    }
                    "min" => {
                        let min = U256::zero();
                        let c = Concrete::from(min);
                        let node = self.add_node(Node::Concrete(c)).into();
                        let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                            .into_expr_err(loc)?;
                        var.name = format!("int{size}.min");
                        var.display_name = var.name.clone();
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok(ExprRet::Single(cvar))
                    }
                    e => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!(
                            "Unknown type attribute on uint{size}: {e:?}, ctx: {}",
                            ctx.path(self)
                        ),
                    )),
                },
            }
        }
    }

    fn library_func_search(
        &mut self,
        ctx: ContextNode,
        ty: NodeIdx,
        ident: &Identifier,
    ) -> Option<ExprRet> {
        self.possible_library_funcs(ctx, ty)
            .iter()
            .filter_map(|func| {
                if let Ok(name) = func.name(self) {
                    Some((name, func))
                } else {
                    None
                }
            })
            .find_map(|(name, func)| {
                if name == ident.name {
                    Some(ExprRet::Single((*func).into()))
                } else {
                    None
                }
            })
    }

    fn possible_library_funcs(&mut self, ctx: ContextNode, ty: NodeIdx) -> BTreeSet<FunctionNode> {
        let mut funcs: BTreeSet<FunctionNode> = BTreeSet::new();
        if let Some(associated_contract) = ctx.maybe_associated_contract(self).unwrap() {
            // search for contract scoped `using` statements
            funcs.extend(
                self.graph().edges_directed(ty, Direction::Outgoing).filter(|edge| {
                    matches!(*edge.weight(), Edge::LibraryFunction(scope) if scope == associated_contract.into())
                }).map(|edge| edge.target().into()).collect::<BTreeSet<FunctionNode>>()
            );
        }

        // Search for global `using` funcs
        let source = ctx.associated_source(self);
        funcs.extend(
            self.graph().edges_directed(ty, Direction::Outgoing).filter(|edge| {
                matches!(*edge.weight(), Edge::LibraryFunction(scope) if scope == source)
            }).map(|edge| edge.target().into()).collect::<BTreeSet<FunctionNode>>()
        );

        funcs
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn index_access(
        &mut self,
        loc: Loc,
        parent: NodeIdx,
        dyn_builtin: BuiltInNode,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.variable(ident, ctx, None)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(index_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "No index in index access".to_string()))
            };

            if matches!(index_paths, ExprRet::CtxKilled(_)) {
                ctx.push_expr(index_paths, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_index_access(&index_paths, loc, parent.into(), dyn_builtin, ctx)
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn match_index_access(
        &mut self,
        index_paths: &ExprRet,
        loc: Loc,
        parent: ContextVarNode,
        dyn_builtin: BuiltInNode,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match index_paths {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc),
            ExprRet::Single(idx) => {
                let parent = parent.first_version(self);
                let parent_name = parent.name(self).into_expr_err(loc)?;
                let parent_display_name = parent.display_name(self).unwrap();

                tracing::trace!(
                    "Index access: {}[{}]",
                    parent_display_name,
                    ContextVarNode::from(*idx)
                        .display_name(self)
                        .into_expr_err(loc)?
                );
                let parent_ty = dyn_builtin;
                let parent_stor = parent
                    .storage(self)
                    .into_expr_err(loc)?
                    .as_ref()
                    .expect("parent didnt have a storage location?");
                let indexed_var = ContextVar::new_from_index(
                    self,
                    loc,
                    parent_name,
                    parent_display_name,
                    parent_stor.clone(),
                    &parent_ty,
                    ContextVarNode::from(*idx),
                )
                .into_expr_err(loc)?;

                let idx_node = self.add_node(Node::ContextVar(indexed_var));
                self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.add_var(idx_node.into(), self).into_expr_err(loc)?;
                self.add_edge(*idx, idx_node, Edge::Context(ContextEdge::Index));
                ctx.push_expr(ExprRet::Single(idx_node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            e => Err(ExprErr::UnhandledExprRet(
                loc,
                format!("Unhandled expression return in index access: {e:?}"),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn length(
        &mut self,
        loc: Loc,
        input_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(input_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "Attempted to perform member access without a left-hand side".to_string()));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_length(ctx, loc, ret, true)
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn tmp_length(
        &mut self,
        arr: ContextVarNode,
        array_ctx: ContextNode,
        loc: Loc,
    ) -> ContextVarNode {
        let arr = arr.first_version(self);
        let name = format!("{}.length", arr.name(self).unwrap());
        tracing::trace!("Length access: {}", name);
        if let Some(attr_var) = array_ctx.var_by_name_or_recurse(self, &name).unwrap() {
            attr_var.latest_version(self)
        } else {
            let len_var = ContextVar {
                loc: Some(loc),
                name: arr.name(self).unwrap() + ".length",
                display_name: arr.display_name(self).unwrap() + ".length",
                storage: None,
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                is_return: false,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    SolcRange::try_from_builtin(&Builtin::Uint(256)),
                ),
            };
            let len_node = self.add_node(Node::ContextVar(len_var));

            let next_arr = self
                .advance_var_in_ctx(arr.latest_version(self), loc, array_ctx)
                .unwrap();
            if next_arr
                .underlying(self)
                .unwrap()
                .ty
                .is_dyn_builtin(self)
                .unwrap()
            {
                if let Some(r) = next_arr.ref_range(self).unwrap() {
                    let min = r.evaled_range_min(self).unwrap();
                    let max = r.evaled_range_max(self).unwrap();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::from(len_node);
                        let res = next_arr
                            .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::from(len_node);
                        let res = next_arr
                            .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                }
            }

            self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
            self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
            array_ctx.add_var(len_node.into(), self).unwrap();
            len_node.into()
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn match_length(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        elem_path: ExprRet,
        update_len_bound: bool,
    ) -> Result<(), ExprErr> {
        match elem_path {
            ExprRet::Null => {
                ctx.push_expr(ExprRet::Null, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(arr) => {
                let next_arr = self.advance_var_in_ctx(
                    ContextVarNode::from(arr).latest_version(self),
                    loc,
                    ctx,
                )?;
                let arr = ContextVarNode::from(arr).first_version(self);
                let name = format!("{}.length", arr.name(self).into_expr_err(loc)?);
                tracing::trace!("Length access: {}", name);
                if let Some(len_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
                    let len_var = len_var.latest_version(self);
                    let new_len = self.advance_var_in_ctx(len_var, loc, ctx)?;
                    if update_len_bound
                        && next_arr
                            .underlying(self)
                            .into_expr_err(loc)?
                            .ty
                            .is_dyn_builtin(self)
                            .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::from(new_len);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::from(new_len);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }
                    ctx.push_expr(ExprRet::Single(new_len.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let len_var = ContextVar {
                        loc: Some(loc),
                        name,
                        display_name: arr.display_name(self).into_expr_err(loc)? + ".length",
                        storage: None,
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        is_return: false,
                        ty: VarType::BuiltIn(
                            BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                            SolcRange::try_from_builtin(&Builtin::Uint(256)),
                        ),
                    };
                    let len_node = self.add_node(Node::ContextVar(len_var));

                    if next_arr
                        .underlying(self)
                        .into_expr_err(loc)?
                        .ty
                        .is_dyn_builtin(self)
                        .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::from(len_node);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::from(len_node);
                                let res = next_arr
                                    .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }

                    self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
                    self.add_edge(len_node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(len_node.into(), self).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(len_node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
            }
            e => todo!("here: {e:?}"),
        }
    }
}
