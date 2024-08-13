use crate::LibraryAccess;

use graph::{
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ExprRet, Function, FunctionNode,
        FunctionParam, FunctionReturn, TyNode,
    },
    AnalyzerBackend, ContextEdge, Edge, VarType,
};
use shared::{ExprErr, GraphError, IntoExprErr};

use alloy_primitives::{I256, U256};
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
            self.builtin_builtins(ctx, node, name, is_storage, loc)
        }
    }

    fn specialize_ty_fn(
        &mut self,
        node: TyNode,
        name: &str,
    ) -> Result<Option<FunctionNode>, GraphError> {
        match name {
            "unwrap" => {
                let func = self.builtin_fns().get("unwrap").unwrap().clone();
                let inputs = vec![
                    FunctionParam {
                        loc: Loc::Builtin,
                        ty: node.0.into(),
                        order: 0,
                        storage: None,
                        name: None,
                    },
                    FunctionParam {
                        loc: Loc::Builtin,
                        ty: node.0.into(),
                        order: 0,
                        storage: None,
                        name: None,
                    },
                ];
                let outputs = vec![FunctionReturn {
                    loc: Loc::Builtin,
                    ty: node.underlying_ty(self)?,
                    storage: None,
                    name: None,
                }];
                Ok(Some(self.construct_specialized_fn(
                    func.clone(),
                    inputs,
                    outputs,
                )?))
            }
            "wrap" => {
                let func = self.builtin_fns().get("wrap").unwrap().clone();
                let inputs = vec![
                    FunctionParam {
                        loc: Loc::Builtin,
                        ty: node.0.into(),
                        order: 0,
                        storage: None,
                        name: None,
                    },
                    FunctionParam {
                        loc: Loc::Builtin,
                        ty: node.underlying_ty(self)?,
                        order: 0,
                        storage: None,
                        name: None,
                    },
                ];
                let outputs = vec![FunctionReturn {
                    loc: Loc::Builtin,
                    ty: node.0.into(),
                    storage: None,
                    name: None,
                }];
                Ok(Some(self.construct_specialized_fn(
                    func.clone(),
                    inputs,
                    outputs,
                )?))
            }
            _ => Ok(None),
        }
    }

    fn builtin_builtin_fn(
        &mut self,
        node: BuiltInNode,
        name: &str,
        num_inputs: usize,
        is_storage: bool,
    ) -> Result<Option<(FunctionNode, bool)>, GraphError> {
        match node.underlying(self)?.clone() {
            Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                match name {
                    "delegatecall" | "call" | "staticcall" | "send" | "transfer" => {
                        // TODO: check if the address is known to be a certain type and the function signature is known
                        // and call into the function
                        let builtin_name = name.split('(').collect::<Vec<_>>()[0];
                        let func_node =
                            FunctionNode::from(self.builtin_fn_or_maybe_add(builtin_name).unwrap());
                        Ok(Some((func_node, true)))
                    }
                    _ => Ok(None),
                }
            }
            Builtin::String => match name.split('(').collect::<Vec<_>>()[0] {
                "concat" => {
                    let full_name = format!(
                        "concat({})",
                        (0..num_inputs)
                            .map(|_| "string")
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    let specialized =
                        if let Some(specialized) = self.builtin_fn_nodes().get(&full_name) {
                            (*specialized).into()
                        } else {
                            // construct a specialized version of concat
                            let func = self.builtin_fns().get("concat").unwrap().clone();
                            let base_input = FunctionParam {
                                loc: Loc::Builtin,
                                ty: self.builtin_or_add(Builtin::String),
                                order: 0,
                                storage: None,
                                name: None,
                            };
                            let inputs = (0..num_inputs)
                                .map(|_| base_input.clone())
                                .collect::<Vec<_>>();
                            let outputs = vec![FunctionReturn {
                                loc: Loc::Builtin,
                                ty: self.builtin_or_add(Builtin::String),
                                storage: None,
                                name: None,
                            }];
                            self.construct_specialized_fn(func.clone(), inputs, outputs)?
                        };

                    Ok(Some((specialized, false)))
                }
                _ => Ok(None),
            },
            Builtin::DynamicBytes => match name.split('(').collect::<Vec<_>>()[0] {
                "concat" => {
                    let full_name = format!(
                        "concat({})",
                        (0..num_inputs)
                            .map(|_| "bytes")
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    let specialized =
                        if let Some(specialized) = self.builtin_fn_nodes().get(&full_name) {
                            (*specialized).into()
                        } else {
                            // construct a specialized version of concat
                            let func = self.builtin_fns().get("concat").unwrap().clone();
                            let base_input = FunctionParam {
                                loc: Loc::Builtin,
                                ty: self.builtin_or_add(Builtin::DynamicBytes),
                                order: 0,
                                storage: None,
                                name: None,
                            };
                            let inputs = (0..num_inputs)
                                .map(|_| base_input.clone())
                                .collect::<Vec<_>>();
                            let outputs = vec![FunctionReturn {
                                loc: Loc::Builtin,
                                ty: self.builtin_or_add(Builtin::DynamicBytes),
                                storage: None,
                                name: None,
                            }];
                            self.construct_specialized_fn(func.clone(), inputs, outputs)?
                        };

                    Ok(Some((specialized, false)))
                }
                _ => Ok(None),
            },
            Builtin::Array(inner) => {
                if name.starts_with("push") {
                    if is_storage {
                        let empty_push = num_inputs == 0;
                        let self_ty = VarType::try_from_idx(self, node.0.into()).unwrap();
                        let full_name = if empty_push {
                            format!("push({})", self_ty.as_string(self)?)
                        } else {
                            format!(
                                "push({}, {})",
                                self_ty.as_string(self)?,
                                inner.as_string(self)?
                            )
                        };
                        let specialized =
                            if let Some(specialized) = self.builtin_fn_nodes().get(&full_name) {
                                (*specialized).into()
                            } else {
                                // construct a specialized version of concat
                                let func = self.builtin_fns().get("push").unwrap();
                                let inputs = if empty_push {
                                    vec![FunctionParam {
                                        loc: Loc::Builtin,
                                        ty: self_ty.ty_idx(),
                                        order: 0,
                                        storage: None,
                                        name: None,
                                    }]
                                } else {
                                    vec![
                                        FunctionParam {
                                            loc: Loc::Builtin,
                                            ty: self_ty.ty_idx(),
                                            order: 0,
                                            storage: None,
                                            name: None,
                                        },
                                        FunctionParam {
                                            loc: Loc::Builtin,
                                            ty: inner.ty_idx(),
                                            order: 0,
                                            storage: None,
                                            name: None,
                                        },
                                    ]
                                };
                                let outputs = if empty_push {
                                    vec![FunctionReturn {
                                        loc: Loc::Builtin,
                                        ty: inner.ty_idx(),
                                        storage: None,
                                        name: None,
                                    }]
                                } else {
                                    vec![]
                                };
                                self.construct_specialized_fn(func.clone(), inputs, outputs)?
                            };

                        Ok(Some((specialized, true)))
                    } else {
                        Ok(None)
                    }
                } else if name.starts_with("pop") {
                    if is_storage {
                        let self_ty = VarType::try_from_idx(self, node.0.into()).unwrap();
                        let full_name = format!("pop({})", self_ty.as_string(self)?);
                        let specialized =
                            if let Some(specialized) = self.builtin_fn_nodes().get(&full_name) {
                                (*specialized).into()
                            } else {
                                // construct a specialized version of concat
                                let func = self.builtin_fns().get("pop").unwrap();
                                let inputs = vec![FunctionParam {
                                    loc: Loc::Builtin,
                                    ty: self_ty.ty_idx(),
                                    order: 0,
                                    storage: None,
                                    name: None,
                                }];
                                let outputs = vec![FunctionReturn {
                                    loc: Loc::Builtin,
                                    ty: inner.ty_idx(),
                                    storage: None,
                                    name: None,
                                }];
                                self.construct_specialized_fn(func.clone(), inputs, outputs)?
                            };
                        Ok(Some((specialized, true)))
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn construct_specialized_fn(
        &mut self,
        func: Function,
        inputs: Vec<FunctionParam>,
        outputs: Vec<FunctionReturn>,
    ) -> Result<FunctionNode, GraphError> {
        let func_node = FunctionNode::from(self.add_node(func));
        inputs.into_iter().rev().for_each(|input| {
            let input_node = self.add_node(input);
            self.add_edge(input_node, func_node, Edge::FunctionParam);
        });
        outputs.into_iter().for_each(|output| {
            let output_node = self.add_node(output);
            self.add_edge(output_node, func_node, Edge::FunctionReturn);
        });

        let params = func_node.params(self);
        let params_strs = params
            .iter()
            .map(|param| param.ty_str(self).unwrap())
            .collect::<Vec<String>>();
        let underlying_mut = func_node.underlying_mut(self)?;
        let name = underlying_mut.name.as_mut().unwrap();
        let full_name = format!("{}({})", name, params_strs.join(", "));
        name.name.clone_from(&full_name);

        self.add_edge(func_node, self.entry(), Edge::Func);

        self.builtin_fn_nodes_mut()
            .insert(full_name, func_node.0.into());

        Ok(func_node)
    }

    fn builtin_builtins(
        &mut self,
        ctx: ContextNode,
        node: BuiltInNode,
        name: &str,
        is_storage: bool,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        match node.underlying(self).into_expr_err(loc)?.clone() {
            Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                match name {
                    "delegatecall" | "call" | "staticcall" | "send" | "transfer" => {
                        // TODO: check if the address is known to be a certain type and the function signature is known
                        // and call into the function
                        let builtin_name = name.split('(').collect::<Vec<_>>()[0];
                        let func_node = self.builtin_fn_or_maybe_add(builtin_name).unwrap();
                        Ok((ExprRet::Single(func_node), true))
                    }
                    "codehash" => {
                        // TODO: try to be smarter based on the address input
                        let bn = self.builtin_or_add(Builtin::Bytes(32));
                        let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                            .into_expr_err(loc)?;
                        let node = self.add_node(cvar);
                        ctx.add_var(node.into(), self).into_expr_err(loc)?;
                        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        Ok((ExprRet::Single(node), false))
                    }
                    "code" => {
                        // TODO: try to be smarter based on the address input
                        let bn = self.builtin_or_add(Builtin::DynamicBytes);
                        let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                            .into_expr_err(loc)?;
                        let node = self.add_node(cvar);
                        ctx.add_var(node.into(), self).into_expr_err(loc)?;
                        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        Ok((ExprRet::Single(node), false))
                    }
                    "balance" => {
                        // TODO: try to be smarter based on the address input
                        let bn = self.builtin_or_add(Builtin::Uint(256));
                        let cvar = ContextVar::new_from_builtin(loc, bn.into(), self)
                            .into_expr_err(loc)?;
                        let node = self.add_node(cvar);
                        ctx.add_var(node.into(), self).into_expr_err(loc)?;
                        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        Ok((ExprRet::Single(node), false))
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
                    I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::ONE
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
                        let min = max * I256::MINUS_ONE - I256::ONE;
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
                        U256::from(2).pow(U256::from(size)) - U256::from(1)
                    };
                    let c = Concrete::Uint(size, max);
                    let node = self.add_node(c).into();
                    let mut var =
                        ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
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
                    let min = U256::ZERO;
                    let c = Concrete::from(min);
                    let node = self.add_node(c).into();
                    let mut var =
                        ContextVar::new_from_concrete(loc, ctx, node, self).into_expr_err(loc)?;
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
