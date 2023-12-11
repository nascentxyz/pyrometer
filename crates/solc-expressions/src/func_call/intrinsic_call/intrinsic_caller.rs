use crate::{
    intrinsic_call::{
        AbiCaller, AddressCaller, ArrayCaller, BlockCaller, ConstructorCaller, DynBuiltinCaller,
        MsgCaller, PrecompileCaller, SolidityCaller, TypesCaller,
    },
    ContextBuilder, ExprErr, FuncCaller, IntoExprErr,
};

use graph::{
    nodes::{Builtin, ContextNode, ExprRet},
    AnalyzerBackend, Node,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Loc};

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
{
}

impl<T> IntrinsicFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerParts
{
}
pub trait IntrinsicFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerParts
{
    /// Calls an intrinsic/builtin function call (casts, require, etc.)
    #[tracing::instrument(level = "trace", skip_all)]
    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
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
                            self.types_call(func_name.name.clone(), input_exprs, *loc, ctx)
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
                self.parse_inputs(ctx, *loc, input_exprs)?;

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
