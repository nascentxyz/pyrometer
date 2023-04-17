use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{context::exprs::variable::Variable, ContextBuilder, ExprRet, NodeIdx};
use shared::analyzer::Search;
use shared::range::elem_ty::Dynamic;
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
    fn visible_member_funcs(&mut self, ctx: ContextNode, member_idx: NodeIdx) -> Vec<FunctionNode> {
        match self.node(member_idx) {
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Contract(con_node), _) => con_node.funcs(self),
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
                VarType::User(TypeNode::Func(func_node), _) => self
                    .possible_library_funcs(ctx, func_node.0.into())
                    .into_iter()
                    .collect::<Vec<_>>(),
            },
            Node::Contract(_) => ContractNode::from(member_idx).funcs(self),
            Node::Concrete(_)
            | Node::Struct(_)
            | Node::Function(_)
            | Node::Enum(_)
            | Node::Builtin(_) => self
                .possible_library_funcs(ctx, member_idx)
                .into_iter()
                .collect::<Vec<_>>(),
            _ => todo!(),
        }
    }

    /// Gets the array type
    #[tracing::instrument(level = "trace", skip_all)]
    fn member_access(
        &mut self,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        // TODO: this is wrong as it overwrites a function call of the form elem.length(...) i believe
        if ident.name == "length" {
            return self.length(loc, member_expr, ctx);
        }

        let ret = self.parse_ctx_expr(member_expr, ctx)?;
        self.match_member(loc, ident, ret)
    }

    fn match_member(
        &mut self,
        loc: Loc,
        ident: &Identifier,
        ret: ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Single((ctx, idx)) | ExprRet::SingleLiteral((ctx, idx)) => {
                self.member_access_inner(loc, idx, ident, ctx)
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|ret| self.match_member(loc, ident, ret))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_member(loc, ident, *w1)?),
                Box::new(self.match_member(loc, ident, *w2)?),
            )),
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
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
            Node::ContextVar(cvar) => match &cvar.ty {
                VarType::User(TypeNode::Struct(struct_node), _) => {
                    let name = format!(
                        "{}.{}",
                        ContextVarNode::from(member_idx)
                            .name(self)
                            .into_expr_err(loc)?,
                        ident.name
                    );
                    tracing::trace!("Struct member access: {}", name);
                    if let Some(attr_var) =
                        ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)?
                    {
                        return Ok(ExprRet::Single((ctx, attr_var.latest_version(self).into())));
                    } else if let Some(field) = struct_node.find_field(self, ident) {
                        if let Some(field_cvar) = ContextVar::maybe_new_from_field(
                            self,
                            loc,
                            cvar,
                            field.underlying(self).unwrap().clone(),
                        ) {
                            let fc_node = self.add_node(Node::ContextVar(field_cvar));
                            self.add_edge(
                                fc_node,
                                ContextVarNode::from(member_idx).first_version(self),
                                Edge::Context(ContextEdge::AttrAccess),
                            );
                            self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                            return Ok(ExprRet::Single((ctx, fc_node)));
                        }
                    } else if let Some(ret) =
                        self.library_func_search(ctx, struct_node.0.into(), ident)
                    {
                        return Ok(ret);
                    }
                }
                VarType::User(TypeNode::Enum(enum_node), _) => {
                    let name = format!(
                        "{}.{}",
                        ContextVarNode::from(member_idx)
                            .name(self)
                            .into_expr_err(loc)?,
                        ident.name
                    );
                    tracing::trace!("Enum member access: {}", name);

                    if let Some(variant) = enum_node
                        .variants(self)
                        .into_expr_err(loc)?
                        .iter()
                        .find(|variant| **variant == name)
                    {
                        let var = ContextVar::new_from_enum_variant(
                            self,
                            ctx,
                            loc,
                            *enum_node,
                            variant.to_string(),
                        )
                        .into_expr_err(loc)?;
                        let cvar = self.add_node(Node::ContextVar(var));
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single((ctx, cvar)));
                    } else if let Some(ret) =
                        self.library_func_search(ctx, enum_node.0.into(), ident)
                    {
                        return Ok(ret);
                    }
                }
                VarType::User(TypeNode::Contract(con_node), _) => {
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
                        if let Some(func_cvar) =
                            ContextVar::maybe_from_user_ty(self, loc, func.0.into())
                        {
                            let fn_node = self.add_node(Node::ContextVar(func_cvar));
                            self.add_edge(
                                fn_node,
                                member_idx,
                                Edge::Context(ContextEdge::FuncAccess),
                            );
                            return Ok(ExprRet::Single((ctx, fn_node)));
                        }
                    } else {
                        match &*ident.name {
                            "name" => {
                                let c = Concrete::from(con_node.name(self).unwrap());
                                let cnode = self.add_node(Node::Concrete(c));
                                let cvar = ContextVar::new_from_concrete(loc, cnode.into(), self)
                                    .into_expr_err(loc)?;
                                let node = self.add_node(Node::ContextVar(cvar));
                                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, node)));
                            }
                            "creationCode" | "runtimeCode" => {
                                let bn = self.builtin_or_add(Builtin::DynamicBytes);
                                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                    .into_expr_err(loc)?;
                                let node = self.add_node(Node::ContextVar(cvar));
                                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, node)));
                            }
                            "interfaceId" => {
                                // TODO: actually calculate this
                                let bn = self.builtin_or_add(Builtin::Bytes(4));
                                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                    .into_expr_err(loc)?;
                                let node = self.add_node(Node::ContextVar(cvar));
                                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, node)));
                            }
                            _ => {
                                return Err(ExprErr::ContractFunctionNotFound(
                                    loc,
                                    format!(
                                    "No function with name {:?} in contract: {:?}. Functions: {:?}",
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
                VarType::BuiltIn(bn, _) => {
                    return self.builtin_member_access(
                        loc,
                        ctx,
                        *bn,
                        ContextVarNode::from(member_idx)
                            .is_storage(self)
                            .into_expr_err(loc)?,
                        ident,
                    );
                }
                e => {
                    return Err(ExprErr::UnhandledCombo(
                        loc,
                        format!("Unhandled member access: {:?}, {:?}", e, ident),
                    ))
                }
            },
            Node::Msg(_msg) => {
                let name = format!("msg.{}", ident.name);
                tracing::trace!("Msg Env member access: {}", name);

                if let Some(attr_var) =
                    ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)?
                {
                    return Ok(ExprRet::Single((ctx, attr_var.latest_version(self).into())));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                        ContextVar::new_from_concrete(loc, node, self).into_expr_err(loc)?;
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    return Ok(ExprRet::Single((ctx, cvar)));
                }
            }
            Node::Block(_b) => {
                let name = format!("block.{}", ident.name);
                tracing::trace!("Block Env member access: {}", name);
                if let Some(attr_var) =
                    ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)?
                {
                    return Ok(ExprRet::Single((ctx, attr_var.latest_version(self).into())));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                return Ok(ExprRet::Single((ctx, cvar)));
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
                        ContextVar::new_from_concrete(loc, node, self).into_expr_err(loc)?;
                    var.name = name.clone();
                    var.display_name = name;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                    return Ok(ExprRet::Single((ctx, cvar)));
                }
            }
            Node::Builtin(ref _b) => {
                return self.builtin_member_access(
                    loc,
                    ctx,
                    BuiltInNode::from(member_idx),
                    false,
                    ident,
                );
            }
            e => {
                return Err(ExprErr::Todo(
                    loc,
                    format!("Member access on type: {e:?} is not yet supported"),
                ))
            }
        }
        Ok(ExprRet::Single((ctx, member_idx)))
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
                        "delegatecall(address, bytes)"
                        | "call(address, bytes)"
                        | "staticcall(address, bytes)" => {
                            // TODO: check if the address is known to be a certain type and the function signature is known
                            // and call into the function
                            let builtin_name = ident.name.split('(').collect::<Vec<_>>()[0];
                            let func = self.builtin_fns().get(builtin_name).unwrap();
                            let (inputs, outputs) = self
                                .builtin_fn_inputs()
                                .get(builtin_name)
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
                        }
                        "code" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "codehash" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Bytes(32));
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "balance" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Uint(256));
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        _ if ident.name.starts_with("send") => {
                            let bn = self.builtin_or_add(Builtin::Bool);
                            let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                                .into_expr_err(loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        _ if ident.name.starts_with("transfer") => Ok(ExprRet::Multi(vec![])),
                        _ => Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!("Unknown member access on address: {:?}", ident.name),
                        )),
                    }
                }
                Builtin::Bool => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on bool: {:?}", ident.name),
                )),
                Builtin::String => match ident.name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let as_fn = self.builtin_fns().get("concat").unwrap();
                        let fn_node = FunctionNode::from(self.add_node(as_fn.clone()));
                        Ok(ExprRet::Single((ctx, fn_node.into())))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!("Unknown member access on string: {:?}", ident.name),
                    )),
                },
                Builtin::Bytes(size) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on bytes{}: {:?}", size, ident.name),
                )),
                Builtin::Rational => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on rational: {:?}", ident.name),
                )),
                Builtin::DynamicBytes => match ident.name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let as_fn = self.builtin_fns().get("concat").unwrap();
                        let fn_node = FunctionNode::from(self.add_node(as_fn.clone()));
                        Ok(ExprRet::Single((ctx, fn_node.into())))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!("Unknown member access on bytes: {:?}", ident.name),
                    )),
                },
                Builtin::Array(_) => {
                    if ident.name.starts_with("push") {
                        if is_storage {
                            let as_fn = self.builtin_fns().get("push").unwrap();
                            let fn_node = FunctionNode::from(self.add_node(as_fn.clone()));
                            Ok(ExprRet::Single((ctx, fn_node.into())))
                        } else {
                            Err(ExprErr::NonStoragePush(
                                loc,
                                "Trying to push to nonstorage variable is not supported"
                                    .to_string(),
                            ))
                        }
                    } else {
                        Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!("Unknown member access on array[]: {:?}", ident.name),
                        ))
                    }
                }
                Builtin::Mapping(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on mapping: {:?}", ident.name),
                )),
                Builtin::Func(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on func: {:?}", ident.name),
                )),
                Builtin::Int(size) => {
                    let max = if size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::from(1)
                    };
                    match &*ident.name {
                        "max" => {
                            let c = Concrete::from(max);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.max");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "min" => {
                            let min = max * I256::from(-1i32);
                            let c = Concrete::from(min);
                            let node = self.add_node(Node::Concrete(c)).into();
                            let mut var = ContextVar::new_from_concrete(loc, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.min");
                            var.display_name = var.name.clone();
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(Node::ContextVar(var));
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        e => Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!("Unknown type attribute on int{size}: {e:?}"),
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
                        let c = Concrete::from(max);
                        let node = self.add_node(Node::Concrete(c)).into();
                        let mut var =
                            ContextVar::new_from_concrete(loc, node, self).into_expr_err(loc)?;
                        var.name = format!("uint{size}.max");
                        var.display_name = var.name.clone();
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(Node::ContextVar(var));
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok(ExprRet::Single((ctx, cvar)))
                    }
                    "min" => {
                        let min = U256::zero();
                        let c = Concrete::from(min);
                        let node = self.add_node(Node::Concrete(c)).into();
                        let mut var =
                            ContextVar::new_from_concrete(loc, node, self).into_expr_err(loc)?;
                        var.name = format!("int{size}.min");
                        var.display_name = var.name.clone();
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(Node::ContextVar(var));
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok(ExprRet::Single((ctx, cvar)))
                    }
                    e => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!("Unknown type attribute on uint{size}: {e:?}"),
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
        if let Some(associated_contract) = ctx.maybe_associated_contract(self).unwrap() {
            // search for local library based functions
            let using_func_children =
                self.search_children(ty, &Edge::LibraryFunction(associated_contract.into()));
            if let Some(found_fn) = using_func_children
                .iter()
                .find(|child| FunctionNode::from(**child).name(self).unwrap() == ident.name)
            {
                let cvar = ContextVar::new_from_func(self, (*found_fn).into()).unwrap();
                let cvar_node = self.add_node(Node::ContextVar(cvar));
                return Some(ExprRet::Single((ctx, cvar_node)));
            }

            // search for local library contracts
            let using_libs_children =
                self.search_children(ty, &Edge::LibraryContract(associated_contract.into()));
            if let Some(found_fn) = using_libs_children.iter().find_map(|lib_contract| {
                ContractNode::from(*lib_contract)
                    .funcs(self)
                    .into_iter()
                    .find(|func| func.name(self).unwrap() == ident.name)
            }) {
                let cvar = ContextVar::new_from_func(self, found_fn).unwrap();
                let cvar_node = self.add_node(Node::ContextVar(cvar));
                return Some(ExprRet::Single((ctx, cvar_node)));
            }
        }

        // Search for global funcs
        let source = ctx.associated_source(self);
        let using_func_children = self.search_children(ty, &Edge::LibraryFunction(source));
        if let Some(found_fn) = using_func_children
            .iter()
            .find(|child| FunctionNode::from(**child).name(self).unwrap() == ident.name)
        {
            let cvar = ContextVar::new_from_func(self, (*found_fn).into()).unwrap();
            let cvar_node = self.add_node(Node::ContextVar(cvar));
            return Some(ExprRet::Single((ctx, cvar_node)));
        }

        // search for global library contracts
        let using_libs_children = self.search_children(ty, &Edge::LibraryContract(source));
        if let Some(found_fn) = using_libs_children.iter().find_map(|lib_contract| {
            ContractNode::from(*lib_contract)
                .funcs(self)
                .into_iter()
                .find(|func| func.name(self).unwrap() == ident.name)
        }) {
            let cvar = ContextVar::new_from_func(self, found_fn).unwrap();
            let cvar_node = self.add_node(Node::ContextVar(cvar));
            return Some(ExprRet::Single((ctx, cvar_node)));
        }

        None
    }

    fn possible_library_funcs(&mut self, ctx: ContextNode, ty: NodeIdx) -> BTreeSet<FunctionNode> {
        let mut funcs: BTreeSet<FunctionNode> = BTreeSet::new();
        if let Some(associated_contract) = ctx.maybe_associated_contract(self).unwrap() {
            // search for local library based functions
            funcs.extend(
                self.search_children(ty, &Edge::LibraryFunction(associated_contract.into()))
                    .into_iter()
                    .map(FunctionNode::from)
                    .collect::<Vec<_>>(),
            );

            // search for local library contracts
            let using_libs_children =
                self.search_children(ty, &Edge::LibraryContract(associated_contract.into()));
            funcs.extend(
                using_libs_children
                    .iter()
                    .flat_map(|lib_contract| ContractNode::from(*lib_contract).funcs(self))
                    .collect::<Vec<_>>(),
            );
        }

        // Search for global funcs
        let source = ctx.associated_source(self);
        funcs.extend(
            self.search_children(ty, &Edge::LibraryFunction(source))
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>(),
        );

        let using_libs_children = self.search_children(ty, &Edge::LibraryContract(source));
        funcs.extend(
            using_libs_children
                .iter()
                .flat_map(|lib_contract| ContractNode::from(*lib_contract).funcs(self))
                .collect::<BTreeSet<_>>(),
        );

        funcs
    }

    fn index_access(
        &mut self,
        loc: Loc,
        parent: NodeIdx,
        dyn_builtin: BuiltInNode,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let index_paths = self.variable(ident, ctx)?;
        self.match_index_access(&index_paths, loc, parent.into(), dyn_builtin, ctx)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn match_index_access(
        &mut self,
        index_paths: &ExprRet,
        loc: Loc,
        parent: ContextVarNode,
        dyn_builtin: BuiltInNode,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        match index_paths {
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
            ExprRet::Single((_index_ctx, idx)) => {
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
                self.add_edge(*idx, idx_node, Edge::Context(ContextEdge::Index));
                Ok(ExprRet::Single((ctx, idx_node)))
            }
            e => Err(ExprErr::UnhandledExprRet(
                loc,
                format!("Unhandled expression return in index access: {e:?}"),
            )),
        }
    }

    fn length(
        &mut self,
        loc: Loc,
        input_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let elem = self.parse_ctx_expr(input_expr, ctx)?;
        self.match_length(loc, elem, true)
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
                if let Some(r) = next_arr.range(self).unwrap() {
                    let min = r.evaled_range_min(self).unwrap();
                    let max = r.evaled_range_max(self).unwrap();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_node));
                        let res = next_arr
                            .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_node));
                        let res = next_arr
                            .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                }
            }

            self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
            self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
            len_node.into()
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn match_length(
        &mut self,
        loc: Loc,
        elem_path: ExprRet,
        update_len_bound: bool,
    ) -> Result<ExprRet, ExprErr> {
        match elem_path {
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
            ExprRet::Single((array_ctx, arr)) => {
                let next_arr = self.advance_var_in_ctx(
                    ContextVarNode::from(arr).latest_version(self),
                    loc,
                    array_ctx,
                )?;
                let arr = ContextVarNode::from(arr).first_version(self);
                let name = format!("{}.length", arr.name(self).into_expr_err(loc)?);
                tracing::trace!("Length access: {}", name);
                if let Some(len_var) = array_ctx
                    .var_by_name_or_recurse(self, &name)
                    .into_expr_err(loc)?
                {
                    let len_var = len_var.latest_version(self);
                    let new_len = self.advance_var_in_ctx(len_var, loc, array_ctx)?;
                    if update_len_bound
                        && next_arr
                            .underlying(self)
                            .into_expr_err(loc)?
                            .ty
                            .is_dyn_builtin(self)
                            .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(new_len.into()));
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(new_len.into()));
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }
                    Ok(ExprRet::Single((array_ctx, new_len.into())))
                } else {
                    let len_var = ContextVar {
                        loc: Some(loc),
                        name,
                        display_name: arr.display_name(self).into_expr_err(loc)? + ".length",
                        storage: None,
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
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
                        if let Some(r) = next_arr.range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(len_node));
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::Dynamic(Dynamic::new(len_node));
                                let res = next_arr
                                    .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }

                    self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
                    self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single((array_ctx, len_node)))
                }
            }
            _ => todo!("here"),
        }
    }
}
