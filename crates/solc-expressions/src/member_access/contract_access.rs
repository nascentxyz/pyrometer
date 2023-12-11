use crate::{ExprErr, IntoExprErr};

use graph::{
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ContractNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> ContractAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for performing member access on a Contract
pub trait ContractAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform member access on a contract
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
}
