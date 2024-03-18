use crate::func_call::intrinsic_call::AddressCaller;
use crate::{ExprErr, IntoExprErr, LibraryAccess};

use graph::{
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use ethers_core::types::{I256, U256};
use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> BuiltinAccess for T where
    T: LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}

/// Trait for performing member access on builtin types
pub trait BuiltinAccess:
    LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Perform member access on builtin types
    fn builtin_member_access(
        &mut self,
        loc: Loc,
        ctx: ContextNode,
        node: BuiltInNode,
        is_storage: bool,
        ident: &Identifier,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!("Looking for builtin member function");
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
                Builtin::SizedArray(s, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on array[{s}]: {:?}, ctx: {}",
                        ident.name,
                        ctx.path(self)
                    ),
                )),
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
                        var.name = format!("uint{size}.min");
                        var.display_name = var.name.clone();
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(Node::ContextVar(var));
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok(ExprRet::Single(cvar))
                    }
                    "call" | "delegatecall" | "staticcall" if size == 160 => {
                        let builtin_name = ident.name.split('(').collect::<Vec<_>>()[0];
                        let func_node = self.builtin_fn_or_maybe_add(builtin_name).unwrap();
                        Ok(ExprRet::Single(func_node))
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
}
