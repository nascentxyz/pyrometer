use crate::{
    func_call::helper::CallerHelper, func_call::modifier::ModifierCaller, ExprErr, IntoExprErr,
};

use graph::{
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::StorageLocation;

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> Env for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles environment based things like `msg`, `block`, etc.
pub trait Env: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn env_variable(
        &mut self,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<Option<()>, ExprErr> {
        match &*ident.name {
            "msg" | "tx" => {
                ctx.add_gas_cost(self, shared::gas::BIN_OP_GAS)
                    .into_expr_err(ident.loc)?;
                ctx.push_expr(ExprRet::Single(self.msg().into()), self)
                    .into_expr_err(ident.loc)?;
                Ok(Some(()))
            }
            "block" => {
                ctx.add_gas_cost(self, shared::gas::BIN_OP_GAS)
                    .into_expr_err(ident.loc)?;
                ctx.push_expr(ExprRet::Single(self.block().into()), self)
                    .into_expr_err(ident.loc)?;
                Ok(Some(()))
            }
            "abi" => Ok(Some(())),
            "_" => {
                #[allow(clippy::manual_map)]
                if let Some(mod_state) = &ctx
                    .underlying(self)
                    .into_expr_err(ident.loc)?
                    .modifier_state
                    .clone()
                {
                    ctx.add_gas_cost(self, shared::gas::FUNC_CALL_GAS)
                        .into_expr_err(ident.loc)?;
                    self.resume_from_modifier(ctx, mod_state.clone())?;
                    self.modifier_inherit_return(ctx, mod_state.parent_ctx);
                    Ok(Some(()))
                } else {
                    Ok(None)
                }
            }
            _e => Ok(None),
        }
    }

    fn block_access(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        ident_name: &str,
    ) -> Result<ExprRet, ExprErr> {
        let name = format!("block.{}", ident_name);
        tracing::trace!("Block Env member access: {}", name);
        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            Ok(ExprRet::Single(attr_var.latest_version(self).into()))
        } else {
            let (node, name) = match ident_name {
                "hash" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.hash {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "basefee" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.basefee {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "chainid" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.chainid {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "coinbase" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.coinbase {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "difficulty" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.difficulty {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "gaslimit" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.gaslimit {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "number" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.number {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "prevrandao" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.prevrandao {
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
                        var.storage = Some(StorageLocation::Block(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "timestamp" => {
                    if let Some(d) = self.block().underlying(self).into_expr_err(loc)?.timestamp {
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
                        var.storage = Some(StorageLocation::Block(loc));
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
            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
            var.name.clone_from(&name);
            var.display_name = name;
            var.is_tmp = false;
            var.is_symbolic = true;
            var.storage = Some(StorageLocation::Block(loc));
            let cvar = self.add_node(Node::ContextVar(var));
            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
            Ok(ExprRet::Single(cvar))
        }
    }

    fn msg_access(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        ident_name: &str,
    ) -> Result<ExprRet, ExprErr> {
        let name = format!("msg.{}", ident_name);
        tracing::trace!("Msg Env member access: {}", name);

        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            Ok(ExprRet::Single(attr_var.latest_version(self).into()))
        } else {
            let (node, name) = match ident_name {
                "data" => {
                    if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.data.clone() {
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
                        var.storage = Some(StorageLocation::Msg(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "sender" => {
                    if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.sender {
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
                        var.storage = Some(StorageLocation::Msg(loc));
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
                        var.storage = Some(StorageLocation::Msg(loc));
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
                        var.storage = Some(StorageLocation::Msg(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "origin" => {
                    if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.origin {
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
                        var.storage = Some(StorageLocation::Msg(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "gasprice" => {
                    if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.gasprice {
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
                        var.storage = Some(StorageLocation::Msg(loc));
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        return Ok(ExprRet::Single(cvar));
                    }
                }
                "gaslimit" => {
                    if let Some(d) = self.msg().underlying(self).into_expr_err(loc)?.gaslimit {
                        let c = Concrete::from(d);
                        (self.add_node(Node::Concrete(c)).into(), "".to_string())
                    } else {
                        let node = self.builtin_or_add(Builtin::Uint(64));
                        let mut var = ContextVar::new_from_builtin(loc, node.into(), self)
                            .into_expr_err(loc)?;
                        var.is_tmp = false;
                        var.is_symbolic = true;
                        var.storage = Some(StorageLocation::Msg(loc));
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

            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
            var.name.clone_from(&name);
            var.display_name = name;
            var.is_tmp = false;
            var.is_symbolic = true;
            var.storage = Some(StorageLocation::Msg(loc));
            let cvar = self.add_node(Node::ContextVar(var));
            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
            Ok(ExprRet::Single(cvar))
        }
    }
}
