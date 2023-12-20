use crate::func_call::func_caller::FuncCaller;
use crate::context_builder::ExpressionParser;
use graph::nodes::ContextVarNode;
use crate::func_caller::NamedOrUnnamedArgs;
use graph::nodes::ContractNode;
use graph::nodes::ContextVar;
use crate::{
    func_call::helper::CallerHelper,
    intrinsic_call::{
        AbiCaller, AddressCaller, ArrayCaller, BlockCaller, ConstructorCaller, DynBuiltinCaller,
        MsgCaller, PrecompileCaller, SolidityCaller, TypesCaller,
    },
    ContextBuilder, ExprErr, IntoExprErr,
};

use graph::{
    nodes::{Builtin, ContextNode, ExprRet},
    AnalyzerBackend, Node,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Loc};

/// Supertrait of individual types of calls like abi, address, etc.
pub trait CallerParts:
    AbiCaller
    + AddressCaller
    + ArrayCaller
    + BlockCaller
    + DynBuiltinCaller
    + PrecompileCaller
    + SolidityCaller
    + TypesCaller
    + ConstructorCaller
    + MsgCaller
    + CallerHelper
{
}

impl<T> CallerParts for T where
    T: AbiCaller
        + AddressCaller
        + ArrayCaller
        + BlockCaller
        + DynBuiltinCaller
        + PrecompileCaller
        + SolidityCaller
        + TypesCaller
        + ConstructorCaller
        + MsgCaller
        + CallerHelper
{
}

impl<T> IntrinsicFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerParts
{
}

/// Perform calls to intrinsic functions like `abi.encode`, `array.push`, `require`, and constructors etc.
pub trait IntrinsicFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerParts
{
    fn new_call(
        &mut self,
        loc: &Loc,
        ty_expr: &Expression,
        inputs: &[Expression],
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(ty_expr, ctx)?;
        self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
            let Some(ty) =
                ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
            else {
                return Err(ExprErr::NoLhs(
                    loc,
                    "No type given for call to `new`".to_string(),
                ));
            };
            let ty_idx = ty.expect_single().into_expr_err(loc)?;
            match analyzer.node(ty_idx) {
                Node::Builtin(Builtin::Array(_)) | Node::Builtin(Builtin::DynamicBytes) => {
                    // construct a new list
                    analyzer.construct_array(ty_idx, &NamedOrUnnamedArgs::Unnamed(inputs), loc, ctx)
                }
                Node::Contract(_c) => {
                    let cnode = ContractNode::from(ty_idx);
                    if let Some(constructor) = cnode.constructor(analyzer) {
                        let params = constructor.params(analyzer);
                        if params.is_empty() {
                            // call the constructor
                            let inputs = ExprRet::Multi(vec![]);
                            analyzer.func_call(
                                ctx,
                                loc,
                                &inputs,
                                constructor,
                                None,
                                None,
                            )?;
                            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                let var = match ContextVar::maybe_from_user_ty(analyzer, loc, ty_idx) {
                                    Some(v) => v,
                                    None => {
                                        return Err(ExprErr::VarBadType(
                                            loc,
                                            format!(
                                                "Could not create context variable from user type: {:?}",
                                                analyzer.node(ty_idx)
                                            ),
                                        ))
                                    }
                                };
                                let contract_cvar =
                                    ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                                ctx.push_expr(ExprRet::Single(contract_cvar.into()), analyzer)
                                    .into_expr_err(loc)
                            })
                        } else {
                            analyzer.parse_inputs(ctx, loc, inputs)?;
                            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                let Some(input_paths) =
                                    ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                                else {
                                    return Err(ExprErr::NoRhs(
                                        loc,
                                        "No inputs for constructor and expected some".to_string(),
                                    ));
                                };
                                // call the constructor
                                analyzer.func_call(
                                    ctx,
                                    loc,
                                    &input_paths,
                                    constructor,
                                    None,
                                    None,
                                )?;
                                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                    let var = match ContextVar::maybe_from_user_ty(analyzer, loc, ty_idx) {
                                        Some(v) => v,
                                        None => {
                                            return Err(ExprErr::VarBadType(
                                                loc,
                                                format!(
                                                    "Could not create context variable from user type: {:?}",
                                                    analyzer.node(ty_idx)
                                                ),
                                            ))
                                        }
                                    };
                                    let contract_cvar =
                                        ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                                    ctx.push_expr(ExprRet::Single(contract_cvar.into()), analyzer)
                                        .into_expr_err(loc)
                                })
                            })
                        }
                    } else {
                        let var = match ContextVar::maybe_from_user_ty(analyzer, loc, ty_idx) {
                            Some(v) => v,
                            None => {
                                return Err(ExprErr::VarBadType(
                                    loc,
                                    format!(
                                        "Could not create context variable from user type: {:?}",
                                        analyzer.node(ty_idx)
                                    ),
                                ))
                            }
                        };
                        let contract_cvar =
                            ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                        ctx.push_expr(ExprRet::Single(contract_cvar.into()), analyzer)
                            .into_expr_err(loc)
                    }
                }
                e => Err(ExprErr::ParseError(loc, format!("Tried to construct a new element of a type ({e:?}) that doesn't support the `new` keyword")))
            }
        })
    }

    /// Calls an intrinsic/builtin function call (casts, require, etc.)
    #[tracing::instrument(level = "trace", skip_all)]
    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &NamedOrUnnamedArgs,
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        // abi
                        _ if func_name.name.starts_with("abi.") => {
                            self.abi_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // address
                        "delegatecall" | "staticcall" | "call" | "code" | "balance" => {
                            self.address_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // array
                        "push" | "pop" => {
                            self.array_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // block
                        "blockhash" => {
                            self.block_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // dynamic sized builtins
                        "concat" => {
                            self.dyn_builtin_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // msg
                        "gasleft" => self.msg_call(func_name.name.clone(), input_exprs, *loc, ctx),
                        // precompiles
                        "sha256" | "ripemd160" | "ecrecover" => self.precompile_call(
                            func_name.name.clone(),
                            func_idx,
                            input_exprs,
                            *loc,
                            ctx,
                        ),
                        // solidity
                        "keccak256" | "addmod" | "mulmod" | "require" | "assert" => {
                            self.solidity_call(func_name.name.clone(), input_exprs, *loc, ctx)
                        }
                        // typing
                        "type" | "wrap" | "unwrap" => {
                            self.types_call(func_name.name.clone(), func_idx, input_exprs, *loc, ctx)
                        }
                        e => Err(ExprErr::Todo(
                            *loc,
                            format!("builtin function: {e:?} doesn't exist or isn't implemented"),
                        )),
                    }
                } else {
                    panic!("unnamed builtin?")
                }
            }
            Node::Builtin(Builtin::Array(_)) => {
                // construct a new array
                self.construct_array(func_idx, input_exprs, *loc, ctx)
            }
            Node::Contract(_) => {
                // construct a new contract
                self.construct_contract(func_idx, input_exprs, *loc, ctx)
            }
            Node::Struct(_) => {
                // construct a struct
                self.construct_struct(func_idx, input_exprs, *loc, ctx)
            }
            Node::Builtin(ty) => {
                // cast to type
                self.cast(ty.clone(), func_idx, input_exprs, *loc, ctx)
            }
            Node::ContextVar(_c) => {
                // its a user type, just push it onto the stack
                ctx.push_expr(ExprRet::Single(func_idx), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            Node::Unresolved(_) => {
                // Try to give a nice error
                input_exprs.parse(self, ctx, *loc)?;

                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Function call failed".to_string()))
                    };

                    if matches!(inputs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let visible_funcs = ctx.visible_funcs(analyzer).into_expr_err(loc)?
                                    .iter()
                                    .map(|func| func.name(analyzer).unwrap())
                                    .collect::<Vec<_>>();

                    if let Node::Unresolved(ident) = analyzer.node(func_idx) {
                        Err(ExprErr::FunctionNotFound(
                            loc,
                            format!(
                                "Could not find function: \"{}{}\", context: {}, visible functions: {:#?}",
                                ident.name,
                                inputs.try_as_func_input_str(analyzer),
                                ctx.path(analyzer),
                                visible_funcs
                            )
                        ))
                    } else {
                        unreachable!()
                    }
                })
            }
            e => Err(ExprErr::FunctionNotFound(
                *loc,
                format!("Unhandled function call type: {e:?}"),
            )),
        }
    }
}
