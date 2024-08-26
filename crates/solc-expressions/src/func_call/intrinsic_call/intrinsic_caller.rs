use crate::{
    func_call::{func_caller::FuncCaller, helper::CallerHelper},
    intrinsic_call::{
        AbiCaller, AddressCaller, ArrayCaller, BlockCaller, ConstructorCaller, DynBuiltinCaller,
        MsgCaller, PrecompileCaller, SolidityCaller, TypesCaller,
    },
    ContextBuilder,
};
use graph::{
    elem::Elem,
    nodes::{
        Concrete, ContextNode, ContextVar, ContextVarNode, ContractId, ContractNode, EnvCtx,
        ExprRet,
    },
    AnalyzerBackend, Node,
};
use shared::{ExprErr, ExprFlag, IntoExprErr, NodeIdx, RangeArena};

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
    fn new_call_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        ty_idx: NodeIdx,
        inputs: ExprRet,
        loc: Loc,
        env: Option<EnvCtx>,
    ) -> Result<(), ExprErr> {
        match self.node(ty_idx) {
            Node::Builtin(_) => {
                assert!(inputs.len() == 1);
                self.construct_array_inner(arena, ty_idx, inputs, loc, ctx)
            }
            Node::Contract(_)  => {
                let cnode = ContractNode::from(ty_idx);
                let try_catch = if matches!(ctx.peek_expr_flag(self), Some(ExprFlag::Try)) {
                    ctx.take_expr_flag(self);
                    true
                } else {
                    false
                };
                if let Some(constructor) = cnode.constructor(self) {
                    let params = constructor.params(self);
                    if params.is_empty() {
                        // call the constructor
                        let inputs = ExprRet::Multi(vec![]);
                        let id = Some(ContractId::Id(self.increment_contract_id()));
                        self.func_call(
                            arena,
                            ctx,
                            loc,
                            &inputs,
                            constructor,
                            None,
                            None,
                            env,
                            id,
                            try_catch,
                        )?;
                        self.apply_to_edges(ctx, loc, arena, &|analyzer, _arena, ctx, loc| {
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
                        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                            let id = Some(ContractId::Id(analyzer.increment_contract_id()));
                            // call the constructor
                            analyzer.func_call(
                                arena,
                                ctx,
                                loc,
                                &inputs,
                                constructor,
                                None,
                                None,
                                env.clone(),
                                id,
                                try_catch,
                            )?;
                            analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, _arena, ctx, loc| {
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
                    let var = match ContextVar::maybe_from_user_ty(self, loc, ty_idx) {
                        Some(v) => v,
                        None => {
                            return Err(ExprErr::VarBadType(
                                loc,
                                format!(
                                    "Could not create context variable from user type: {:?}",
                                    self.node(ty_idx)
                                ),
                            ))
                        }
                    };
                    let contract_cvar =
                        ContextVarNode::from(self.add_node(var));
                    ctx.push_expr(ExprRet::Single(contract_cvar.into()), self)
                        .into_expr_err(loc)
                }
            }
            e => Err(ExprErr::ParseError(loc, format!("Tried to construct a new element of a type ({e:?}) that doesn't support the `new` keyword")))
        }
    }

    fn call_builtin(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        let name = name.split('(').collect::<Vec<_>>()[0];
        match name {
            // abi
            _ if name.starts_with("abi.") => self.abi_call_inner(ctx, name, inputs, loc),
            // address
            "delegatecall" | "staticcall" | "call" | "send" | "transfer" => {
                self.address_call(ctx, name, loc)
            }
            // array
            "push" | "pop" => self.array_call_inner(arena, ctx, name, inputs, loc),
            // block
            "blockhash" | "blobhash" => self.block_call(ctx, name, inputs, loc),
            // dynamic sized builtins
            "concat" => self.dyn_builtin_call(arena, ctx, name, inputs, loc),
            // msg
            "gasleft" => self.msg_call(ctx, name, loc),
            // precompiles
            "sha256" | "ripemd160" | "ecrecover" => self.precompile_call(ctx, name, inputs, loc),
            // solidity
            "keccak256" | "addmod" | "mulmod" | "require" | "assert" | "selfdestruct" => {
                self.solidity_call(arena, ctx, name, inputs, loc)
            }
            // typing
            "type" | "wrap" | "unwrap" => self.types_call(arena, ctx, name, inputs, loc),
            e => Err(ExprErr::Todo(
                loc,
                format!("builtin function: {e:?} doesn't exist or isn't implemented"),
            )),
        }
    }
}
