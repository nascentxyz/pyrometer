use crate::{assign::Assign, variable::Variable, BinOp, Cmp, Env};

use graph::{
    elem::*,
    nodes::{
        Builtin, Concrete, ConcreteNode, ContextNode, ContextVar, ContextVarNode, ExprRet,
        KilledKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, SolcRange, VarType,
};
use shared::{ExprErr, FlatExpr, IntoExprErr, RangeArena, StorageLocation};

use alloy_primitives::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> YulFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}
pub trait YulFuncCaller:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    fn yul_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        name: &str,
        inputs: ExprRet,
        assembly_block_idx: usize,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match name {
            "caller" => {
                let t = self.msg_access(ctx, "sender", loc)?;
                ctx.push_expr(t, self).into_expr_err(loc)
            }
            "origin" => {
                let t = self.msg_access(ctx, "origin", loc)?;
                ctx.push_expr(t, self).into_expr_err(loc)
            }
            "gasprice" => {
                let t = self.msg_access(ctx, "gasprice", loc)?;
                ctx.push_expr(t, self).into_expr_err(loc)
            }
            "callvalue" => {
                let t = self.msg_access(ctx, "value", loc)?;
                ctx.push_expr(t, self).into_expr_err(loc)
            }
            "pop" => Ok(()),
            "hash" | "basefee" | "chainid" | "coinbase" | "difficulty" | "gaslimit" | "number"
            | "prevrandao" | "timestamp" | "blobhash" | "blobbasefee" => {
                let t = self.block_access(ctx, name, loc)?;
                ctx.push_expr(t, self).into_expr_err(loc)
            }
            "log0" | "log1" | "log2" | "log3" | "log4" => {
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "selfdestruct" => ctx.kill(self, loc, KilledKind::Ended).into_expr_err(loc),
            "stop" | "revert" | "invalid" => {
                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)
            }
            "return" => {
                let [offset, size] = inputs.into_sized();
                self.return_yul(ctx, offset, size, loc)?;
                ctx.kill(self, loc, KilledKind::Ended).into_expr_err(loc)?;
                Ok(())
            }
            "not" => {
                if inputs.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `not` expected 1 argument found: {:?}",
                            inputs.len()
                        ),
                    ));
                }

                let [lhs] = inputs.into_sized();
                self.bit_not_inner(arena, ctx, lhs.flatten(), loc)
            }
            "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod" | "exp" | "and" | "or"
            | "xor" | "shl" | "shr" | "sar" => {
                let op = match name {
                    "add" => RangeOp::Add(true),
                    "sub" => RangeOp::Sub(true),
                    "mul" => RangeOp::Mul(true),
                    "div" | "sdiv" => RangeOp::Div(true),
                    "mod" | "smod" => RangeOp::Mod,
                    "exp" => RangeOp::Exp(true),
                    "and" => RangeOp::BitAnd,
                    "or" => RangeOp::BitOr,
                    "xor" => RangeOp::BitXor,
                    "shl" => RangeOp::Shl,
                    "shr" | "sar" => RangeOp::Shr,
                    _ => unreachable!(),
                };

                if inputs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `{}` expects 2 arguments found: {:?}",
                            name,
                            inputs.len()
                        ),
                    ));
                }

                let [lhs, rhs] = if matches!(name, "shl" | "shr" | "sar") {
                    // yul shifts are super dumb and are reversed.
                    let [rhs, lhs] = inputs.into_sized();
                    [lhs, rhs]
                } else {
                    let [lhs, rhs] = inputs.into_sized();
                    [lhs, rhs]
                };

                // we have to cast the inputs into an EVM word, which is effectively a u256.
                let word_ty = self.builtin_or_add(Builtin::Uint(256));
                let cast_ty = VarType::try_from_idx(self, word_ty).unwrap();
                let lhs_paths = ContextVarNode::from(lhs.expect_single().into_expr_err(loc)?)
                    .as_tmp(self, ctx, loc)
                    .into_expr_err(loc)?;
                lhs_paths
                    .cast_from_ty(cast_ty.clone(), self, arena)
                    .into_expr_err(loc)?;

                let rhs_paths = ContextVarNode::from(rhs.expect_single().into_expr_err(loc)?)
                    .as_tmp(self, ctx, loc)
                    .into_expr_err(loc)?;
                rhs_paths
                    .cast_from_ty(cast_ty, self, arena)
                    .into_expr_err(loc)?;

                self.op_match(
                    arena,
                    ctx,
                    loc,
                    &ExprRet::Single(lhs_paths.latest_version(self).into()),
                    &ExprRet::Single(rhs_paths.latest_version(self).into()),
                    op,
                    false,
                )
            }
            "lt" | "gt" | "slt" | "sgt" | "eq" => {
                let op = match name {
                    "lt" | "slt" => RangeOp::Lt,
                    "gt" | "sgt" => RangeOp::Gt,
                    "eq" => RangeOp::Eq,
                    _ => unreachable!(),
                };

                if inputs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `{}` expects 2 arguments found: {:?}",
                            name,
                            inputs.len()
                        ),
                    ));
                }

                let [lhs_paths, rhs_paths] = inputs.into_sized();

                self.cmp_inner(arena, ctx, loc, &lhs_paths, op, &rhs_paths)?;
                let result = ctx
                    .pop_n_latest_exprs(1, loc, self)
                    .into_expr_err(loc)?
                    .swap_remove(0);

                let res = ContextVarNode::from(result.expect_single().into_expr_err(loc)?);
                let next = self.advance_var_in_ctx(arena, res, loc, ctx)?;
                let expr = Elem::Expr(RangeExpr::new(
                    Elem::from(res),
                    RangeOp::Cast,
                    Elem::from(Concrete::Uint(256, U256::ZERO)),
                ));

                next.set_range_min(self, arena, expr.clone())
                    .into_expr_err(loc)?;
                next.set_range_max(self, arena, expr).into_expr_err(loc)?;
                ctx.push_expr(ExprRet::Single(next.into()), self)
                    .into_expr_err(loc)
            }
            "iszero" => {
                if inputs.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `iszero` expects 1 arguments found: {:?}",
                            inputs.len()
                        ),
                    ));
                }

                let [lhs_paths] = inputs.into_sized();

                let cnode = ConcreteNode::from(self.add_node(Concrete::from(U256::ZERO)));
                let tmp_true = ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                    .into_expr_err(loc)?;
                let rhs_paths =
                    ExprRet::Single(ContextVarNode::from(self.add_node(tmp_true)).into());

                self.cmp_inner(arena, ctx, loc, &lhs_paths, RangeOp::Eq, &rhs_paths)
            }
            "addmod" | "mulmod" => {
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "msize" | "pc" | "mload" | "sload" | "gas" | "returndatasize" => {
                // TODO: actually handle this. @MemoryModel
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "calldatacopy" => {
                // TODO: actually handle this. @MemoryModel
                Ok(())
            }
            "calldatasize" => {
                // TODO: actually handle this. @MemoryModel
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "calldataload" => {
                if inputs.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `calldataload` expects 1 arguments found: {:?}",
                            inputs.len()
                        ),
                    ));
                }

                let [lhs_paths] = inputs.into_sized();
                // TODO: check const version
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                let elem = ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                var.display_name = format!(
                    "calldata[{}:{}+32]",
                    elem.display_name(self).into_expr_err(loc)?,
                    elem.display_name(self).into_expr_err(loc)?
                );
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "keccak256" => {
                let b = Builtin::Bytes(32);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "call" | "delegatecall" | "callcode" | "staticcall" => {
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b.clone()).into(), self)
                        .into_expr_err(loc)?;
                var.display_name = format!("{name}_success");
                let mut range = SolcRange::try_from_builtin(&b).unwrap();
                range.min = Elem::from(Concrete::from(U256::ZERO));
                range.max = Elem::from(Concrete::from(U256::from(1)));
                var.ty.set_range(range).into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "create" | "create2" => {
                let b = Builtin::Address;
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                var.display_name = format!("{name}_success");
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "returndatacopy" => {
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "byte" => {
                let b = Builtin::Uint(8);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "mstore" | "mstore8" => {
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about memory variables anymore.
                // We should check if the location is a reference to an existing var and update based on that
                // @MemoryModel
                let vars = ctx.local_vars(self).clone();
                vars.into_iter().try_for_each(|(_name, var)| {
                    // widen to any  max range
                    let latest_var = var.latest_version_or_inherited_in_ctx(ctx, self);
                    if matches!(
                        latest_var.underlying(self).into_expr_err(loc)?.storage,
                        Some(StorageLocation::Memory(_))
                    ) {
                        let res = latest_var.ty(self).into_expr_err(loc)?;
                        if let Some(r) = res.default_range(self).unwrap() {
                            let new_var = self
                                .advance_var_in_ctx(arena, latest_var, loc, ctx)
                                .unwrap();
                            let res = new_var.set_range_min(self, arena, r.min).into_expr_err(loc);
                            let _ = self.add_if_err(res);
                            let res = new_var.set_range_max(self, arena, r.max).into_expr_err(loc);
                            let _ = self.add_if_err(res);
                        }
                    }
                    Ok(())
                })?;
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "sstore" => {
                if inputs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `{}` expects 2 arguments found: {:?}",
                            name,
                            inputs.len()
                        ),
                    ));
                }
                let [value, slot] = inputs.into_sized();
                let cvar = ContextVarNode::from(slot.expect_single().unwrap());

                if let Some(slot) = cvar.slot_to_storage(self) {
                    self.match_assign_sides(
                        arena,
                        ctx,
                        loc,
                        &ExprRet::Single(slot.into()),
                        &value,
                    )?;
                } else {
                    // TODO: improve this. We now handle `slot` but should try to figure out storage layout
                    let vars = ctx.local_vars(self).clone();
                    vars.iter().try_for_each(|(_name, var)| {
                        // widen to any  max range
                        let latest_var = var.latest_version(self);
                        if matches!(
                            latest_var.underlying(self).into_expr_err(loc)?.storage,
                            Some(StorageLocation::Storage(_))
                        ) {
                            let res = latest_var.ty(self).into_expr_err(loc)?;
                            if let Some(r) = res.default_range(self).unwrap() {
                                let new_var = self
                                    .advance_var_in_ctx(arena, latest_var, loc, ctx)
                                    .unwrap();
                                let res =
                                    new_var.set_range_min(self, arena, r.min).into_expr_err(loc);
                                let _ = self.add_if_err(res);
                                let res =
                                    new_var.set_range_max(self, arena, r.max).into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                        Ok(())
                    })?;
                }
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "balance" => {
                let [lhs_paths] = inputs.into_sized();

                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                let elem = ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                var.display_name =
                    format!("balance({})", elem.display_name(self).into_expr_err(loc)?);
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "selfbalance" => {
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                var.display_name = "selfbalance()".to_string();
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "address" => {
                let b = Builtin::Address;
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                var.display_name = "address()".to_string();
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "extcodesize" => {
                let [lhs_paths] = inputs.into_sized();
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                let elem = ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                var.display_name = format!(
                    "extcodesize({})",
                    elem.display_name(self).into_expr_err(loc)?
                );
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "codesize" => {
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                var.display_name = "codesize()".to_string();
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "codecopy" => {
                if inputs.len() != 3 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `{}` expects 3 arguments found: {:?}",
                            name,
                            inputs.len()
                        ),
                    ));
                }

                let [_, _, _, _] = inputs.into_sized();
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)
            }
            "extcodecopy" => {
                if inputs.len() != 4 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Yul function: `{}` expects 4 arguments found: {:?}",
                            name,
                            inputs.len()
                        ),
                    ));
                }

                let [_, _, _, _] = inputs.into_sized();
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(loc)
            }
            "extcodehash" => {
                let [lhs_paths] = inputs.into_sized();

                let b = Builtin::Bytes(32);
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(loc)?;
                let elem = ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                var.display_name = format!(
                    "extcodehash({})",
                    elem.display_name(self).into_expr_err(loc)?
                );
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            _ => {
                let assoc_fn = ctx.associated_fn(self).into_expr_err(loc)?;
                let all_yul_fns = assoc_fn.yul_funcs(self, assembly_block_idx);
                if let Some(yul_fn) = all_yul_fns
                    .iter()
                    .find(|yul_fn| yul_fn.name(self).unwrap() == name)
                {
                    let exprs = yul_fn.exprs(self).unwrap().clone();
                    let end = stack.split_off(ctx.parse_idx(self));
                    stack.extend(exprs);
                    stack.extend(end);
                    let inputs = inputs.as_vec();
                    inputs
                        .into_iter()
                        .try_for_each(|i| ctx.push_expr(i, self).into_expr_err(loc))
                } else {
                    Err(ExprErr::Todo(
                        loc,
                        format!("Unhandled yul function: \"{}\"", name),
                    ))
                }
            }
        }
    }

    fn return_yul(
        &mut self,
        ctx: ContextNode,
        _offset: ExprRet,
        size: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match size {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(size) | ExprRet::SingleLiteral(size) => {
                let b = Builtin::DynamicBytes;
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b.clone()).into(), self)
                        .into_expr_err(loc)?;
                let mut range = SolcRange::try_from_builtin(&b).unwrap();
                match &mut range.min {
                    Elem::ConcreteDyn(ref mut r) => r.set_len(Elem::from(size)),
                    _ => unreachable!(),
                }
                match range.max {
                    Elem::ConcreteDyn(ref mut r) => r.set_len(Elem::from(size)),
                    _ => unreachable!(),
                }
                var.is_return = true;
                var.ty.set_range(range).into_expr_err(loc)?;
                let node = self.add_node(var);
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Return));
                ctx.add_return_node(
                    loc,
                    ContextVarNode::from(node).latest_version_or_inherited_in_ctx(ctx, self),
                    self,
                )
                .into_expr_err(loc)
            }
            ExprRet::Multi(sizes) => {
                sizes
                    .into_iter()
                    .try_for_each(|size| self.return_yul(ctx, _offset.clone(), size, loc))?;
                Ok(())
            }
            ExprRet::Null => Ok(()),
        }
    }
}
