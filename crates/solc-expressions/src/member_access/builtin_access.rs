use crate::LibraryAccess;

use graph::{
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr};

use ethers_core::types::{I256, U256};
use solang_parser::pt::{Expression, Loc};

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
        ctx: ContextNode,
        node: BuiltInNode,
        name: &str,
        is_storage: bool,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        tracing::trace!("Looking for builtin member function");
        if let Some(ret) = self.library_func_search(ctx, node.0.into(), name) {
            Ok((ret, true))
        } else {
            match node.underlying(self).into_expr_err(loc)?.clone() {
                Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                    match name {
                        "delegatecall" | "call" | "staticcall" | "code" | "codehash"
                        | "balance" | "send" | "transfer" => {
                            // TODO: check if the address is known to be a certain type and the function signature is known
                            // and call into the function
                            let builtin_name = name.split('(').collect::<Vec<_>>()[0];
                            let func_node = self.builtin_fn_or_maybe_add(builtin_name).unwrap();
                            Ok((ExprRet::Single(func_node), true))
                        }
                        _ => Err(ExprErr::MemberAccessNotFound(
                            loc,
                            format!(
                                "Unknown member access on address: \"{name}\", ctx: {}",
                                ctx.path(self)
                            ),
                        )),
                    }
                }
                Builtin::Bool => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on bool: \"{name}\", ctx: {}",
                        ctx.path(self)
                    ),
                )),
                Builtin::String => match name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let fn_node = self.builtin_fn_or_maybe_add("concat").unwrap();
                        Ok((ExprRet::Single(fn_node), false))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!(
                            "Unknown member access on string: \"{name}\", ctx: {}",
                            ctx.path(self)
                        ),
                    )),
                },
                Builtin::Bytes(size) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!("Unknown member access on bytes{}: {name}", size),
                )),
                Builtin::Rational => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on rational: \"{name}\", ctx: {}",
                        ctx.path(self)
                    ),
                )),
                Builtin::DynamicBytes => match name.split('(').collect::<Vec<_>>()[0] {
                    "concat" => {
                        let fn_node = self.builtin_fn_or_maybe_add("concat").unwrap();
                        Ok((ExprRet::Single(fn_node), false))
                    }
                    _ => Err(ExprErr::MemberAccessNotFound(
                        loc,
                        format!(
                            "Unknown member access on bytes: \"{name}\", ctx: {}",
                            ctx.path(self)
                        ),
                    )),
                },
                Builtin::Array(_) => {
                    if name.starts_with("push") {
                        if is_storage {
                            let fn_node = self.builtin_fn_or_maybe_add("push").unwrap();
                            Ok((ExprRet::Single(fn_node), true))
                        } else {
                            Err(ExprErr::NonStoragePush(
                                loc,
                                "Trying to push to nonstorage array is not supported".to_string(),
                            ))
                        }
                    } else if name.starts_with("pop") {
                        if is_storage {
                            let fn_node = self.builtin_fn_or_maybe_add("pop").unwrap();
                            Ok((ExprRet::Single(fn_node), true))
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
                                "Unknown member access on array[]: \"{name}\", ctx: {}",
                                ctx.path(self)
                            ),
                        ))
                    }
                }
                Builtin::SizedArray(s, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on array[{s}]: \"{name}\", ctx: {}",
                        ctx.path(self)
                    ),
                )),
                Builtin::Mapping(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on mapping: \"{name}\", ctx: {}",
                        ctx.path(self)
                    ),
                )),
                Builtin::Func(_, _) => Err(ExprErr::MemberAccessNotFound(
                    loc,
                    format!(
                        "Unknown member access on func: \"{name}\", ctx: {}",
                        ctx.path(self)
                    ),
                )),
                Builtin::Int(size) => {
                    let max = if size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::from(1)
                    };
                    match name {
                        "max" => {
                            let c = Concrete::Int(size, max);
                            let node = self.add_node(c).into();
                            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.max");
                            var.display_name.clone_from(&var.name);
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(var);
                            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok((ExprRet::Single(cvar), false))
                        }
                        "min" => {
                            let min = max * I256::from(-1i32) - I256::from(1i32);
                            let c = Concrete::Int(size, min);
                            let node = self.add_node(c).into();
                            let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                                .into_expr_err(loc)?;
                            var.name = format!("int{size}.min");
                            var.display_name.clone_from(&var.name);
                            var.is_tmp = true;
                            var.is_symbolic = false;
                            let cvar = self.add_node(var);
                            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            Ok((ExprRet::Single(cvar), false))
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
                Builtin::Uint(size) => match name {
                    "max" => {
                        let max = if size == 256 {
                            U256::MAX
                        } else {
                            U256::from(2).pow(U256::from(size)) - 1
                        };
                        let c = Concrete::Uint(size, max);
                        let node = self.add_node(c).into();
                        let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                            .into_expr_err(loc)?;
                        var.name = format!("uint{size}.max");
                        var.display_name.clone_from(&var.name);
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(var);
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok((ExprRet::Single(cvar), false))
                    }
                    "min" => {
                        let min = U256::zero();
                        let c = Concrete::from(min);
                        let node = self.add_node(c).into();
                        let mut var = ContextVar::new_from_concrete(loc, ctx, node, self)
                            .into_expr_err(loc)?;
                        var.name = format!("uint{size}.min");
                        var.display_name.clone_from(&var.name);
                        var.is_tmp = true;
                        var.is_symbolic = false;
                        let cvar = self.add_node(var);
                        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        Ok((ExprRet::Single(cvar), false))
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
