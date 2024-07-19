use crate::member_access::library_access::LibraryAccess;
use graph::{
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ContractNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> ContractAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for performing member access on a Contract
pub trait ContractAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform member access on a contract
    fn contract_member_access(
        &mut self,
        ctx: ContextNode,
        maybe_parent: Option<ContextVarNode>,
        con_node: ContractNode,
        name: &str,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        tracing::trace!(
            "Contract member access: {}.{}",
            con_node
                .maybe_name(self)
                .into_expr_err(loc)?
                .unwrap_or_else(|| "interface".to_string()),
            name
        );

        if let Some((_, func)) = con_node
            .linearized_functions(self, false)
            .into_expr_err(loc)?
            .into_iter()
            .find(|(func_name, func_node)| func_name == name)
        {
            if let Some(func_cvar) = ContextVar::maybe_from_user_ty(self, loc, func.0.into()) {
                let fn_node = self.add_node(func_cvar);
                // this prevents attaching a dummy node to the parent which could cause a cycle in the graph
                if let Some(parent) = maybe_parent {
                    self.add_edge(fn_node, parent, Edge::Context(ContextEdge::FuncAccess));
                }
                Ok((ExprRet::Single(fn_node), false))
            } else {
                Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unable to construct the function \"{name}\" in contract \"{}\"",
                        con_node.name(self).into_expr_err(loc)?
                    ),
                ))
            }
        } else if let Some(ret) = self.library_func_search(ctx, con_node.0.into(), name) {
            Ok((ret, true))
        } else if let Some(func) = con_node
            .structs(self)
            .into_iter()
            .find(|struct_node| struct_node.name(self).unwrap() == name)
        {
            if let Some(struct_cvar) = ContextVar::maybe_from_user_ty(self, loc, func.0.into()) {
                let struct_node = self.add_node(struct_cvar);
                // this prevents attaching a dummy node to the parent which could cause a cycle in the graph
                if let Some(parent) = maybe_parent {
                    self.add_edge(
                        struct_node,
                        parent,
                        Edge::Context(ContextEdge::StructAccess),
                    );
                }
                return Ok((ExprRet::Single(struct_node), false));
            } else {
                return Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unable to construct the struct \"{name}\" in contract \"{}\"",
                        con_node.name(self).into_expr_err(loc)?
                    ),
                ));
            }
        } else {
            let res = match name {
                "name" => {
                    let c = Concrete::from(con_node.name(self).unwrap());
                    let cnode = self.add_node(c);
                    let cvar = ContextVar::new_from_concrete(loc, ctx, cnode.into(), self)
                        .into_expr_err(loc)?;
                    let node = self.add_node(cvar);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(node))
                }
                "creationCode" | "runtimeCode" => {
                    let bn = self.builtin_or_add(Builtin::DynamicBytes);
                    let cvar =
                        ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(cvar);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(node))
                }
                "interfaceId" => {
                    // TODO: actually calculate this
                    let bn = self.builtin_or_add(Builtin::Bytes(4));
                    let cvar =
                        ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(cvar);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(node))
                }
                _ => {
                    // try to match just prefix
                    if let Some(func) = con_node.funcs(self).into_iter().find(|func_node| {
                        if let Some(prefix) = func_node.prefix_only_name(self).unwrap() {
                            prefix == name
                        } else {
                            false
                        }
                    }) {
                        if let Some(func_cvar) =
                            ContextVar::maybe_from_user_ty(self, loc, func.0.into())
                        {
                            let fn_node = self.add_node(func_cvar);
                            // this prevents attaching a dummy node to the parent which could cause a cycle in the graph
                            if let Some(parent) = maybe_parent {
                                self.add_edge(
                                    fn_node,
                                    parent,
                                    Edge::Context(ContextEdge::FuncAccess),
                                );
                            }
                            Ok(ExprRet::Single(fn_node))
                        } else {
                            Err(ExprErr::MemberAccessNotFound(
                                loc,
                                format!(
                                    "Unable to construct the function \"{name}\" in contract \"{}\"",
                                    con_node.name(self).into_expr_err(loc)?
                                ),
                            ))
                        }
                    } else {
                        Err(ExprErr::ContractFunctionNotFound(
                            loc,
                            format!(
                            "No function or struct with name \"{name}\" in contract: {:?}. Functions: {:#?}",
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
            };
            Ok((res?, false))
        }
    }
}
