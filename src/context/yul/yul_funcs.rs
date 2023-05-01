use crate::context::exprs::BinOp;
use crate::context::exprs::Cmp;
use crate::context::exprs::IntoExprErr;
use crate::context::yul::YulBuilder;
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use crate::Concrete;
use crate::ConcreteNode;
use crate::ExprRet;
use crate::Node;
use ethers_core::types::U256;
use shared::analyzer::AnalyzerLike;
use shared::analyzer::GraphLike;
use shared::range::elem_ty::Dynamic;
use shared::range::{elem_ty::Elem, SolcRange};
use shared::{context::ContextEdge, nodes::Builtin, Edge};
use shared::{context::*, range::elem::RangeOp};
use solang_parser::pt::YulFunctionCall;
use solang_parser::pt::{Expression, Loc, StorageLocation};

impl<T> YulFuncCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
}
pub trait YulFuncCaller:
    GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized
{
    fn yul_func_call(
        &mut self,
        func_call: &YulFunctionCall,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let YulFunctionCall { loc, id, arguments } = func_call;

        match &*id.name {
            "log0" | "log1" | "log2" | "log3" | "log4" => Ok(ExprRet::Multi(vec![])),
            "stop" | "revert" | "selfdestruct" | "invalid" => {
                ctx.kill(self, *loc).into_expr_err(*loc)?;
                Ok(ExprRet::CtxKilled)
            }
            "return" => {
                let size = self.parse_ctx_yul_expr(&arguments[1], ctx)?;
                self.return_yul(*loc, size)?;
                ctx.kill(self, *loc).into_expr_err(*loc)?;
                Ok(ExprRet::CtxKilled)
            }
            "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod" | "exp" | "and" | "or"
            | "xor" | "shl" | "shr" | "sar" => {
                let op = match &*id.name {
                    "add" => RangeOp::Add,
                    "sub" => RangeOp::Sub,
                    "mul" => RangeOp::Mul,
                    "div" | "sdiv" => RangeOp::Div,
                    "mod" | "smod" => RangeOp::Mod,
                    "exp" => RangeOp::Exp,
                    "and" => RangeOp::BitAnd,
                    "or" => RangeOp::BitOr,
                    "xor" => RangeOp::BitXor,
                    "shl" => RangeOp::Shl,
                    "shr" | "sar" => RangeOp::Shr,
                    _ => unreachable!(),
                };

                if arguments.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(
                        *loc,
                        format!(
                            "Yul function: `{}` expects 2 arguments found: {:?}",
                            id.name,
                            arguments.len()
                        ),
                    ));
                }

                let lhs_paths = self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                let rhs_paths = self.parse_ctx_yul_expr(&arguments[1], ctx)?;
                self.op_match(*loc, &lhs_paths, &rhs_paths, op, false)
            }
            "lt" | "gt" | "slt" | "sgt" | "eq" => {
                let op = match &*id.name {
                    "lt" | "slt" => RangeOp::Lt,
                    "gt" | "sgt" => RangeOp::Gt,
                    "eq" => RangeOp::Eq,
                    _ => unreachable!(),
                };

                if arguments.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(
                        *loc,
                        format!(
                            "Yul function: `{}` expects 2 arguments found: {:?}",
                            id.name,
                            arguments.len()
                        ),
                    ));
                }

                let lhs_paths = self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                let rhs_paths = self.parse_ctx_yul_expr(&arguments[1], ctx)?;
                self.cmp_inner(*loc, &lhs_paths, op, &rhs_paths)
            }
            "iszero" => {
                if arguments.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        *loc,
                        format!(
                            "Yul function: `iszero` expects 1 arguments found: {:?}",
                            arguments.len()
                        ),
                    ));
                }
                let lhs_paths = self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                let cnode = ConcreteNode::from(
                    self.add_node(Node::Concrete(Concrete::from(U256::from(0)))),
                );
                let tmp_true = Node::ContextVar(
                    ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                        .into_expr_err(*loc)?,
                );
                let rhs_paths =
                    ExprRet::Single((ctx, ContextVarNode::from(self.add_node(tmp_true)).into()));

                self.cmp_inner(*loc, &lhs_paths, RangeOp::Eq, &rhs_paths)
            }
            "msize" | "pc" | "mload" | "sload" | "gas" | "returndatasize" => {
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single((ctx, node)))
            }
            "keccak256" => {
                let b = Builtin::Bytes(32);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single((ctx, node)))
            }
            "call" | "delegatecall" | "callcode" | "staticcall" => {
                let b = Builtin::Uint(256);
                let mut var =
                    ContextVar::new_from_builtin(*loc, self.builtin_or_add(b.clone()).into(), self)
                        .into_expr_err(*loc)?;
                var.display_name = format!("{id}_success");
                let mut range = SolcRange::try_from_builtin(&b).unwrap();
                range.min = Elem::from(Concrete::from(U256::from(0)));
                range.max = Elem::from(Concrete::from(U256::from(1)));
                var.ty.set_range(range).into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single((ctx, node)))
            }
            "create" | "create2" => {
                let b = Builtin::Address;
                let mut var =
                    ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(*loc)?;
                var.display_name = format!("{id}_success");
                let node = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single((ctx, node)))
            }
            "returndatacopy" => Ok(ExprRet::Multi(vec![])),
            "byte" => {
                let b = Builtin::Uint(8);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                Ok(ExprRet::Single((ctx, node)))
            }
            "mstore" | "mstore8" => {
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about memory variables anymore.
                // We should check if the location is a reference to an existing var and update based on that
                let vars = ctx.local_vars(self);
                vars.iter().try_for_each(|var| {
                    // widen to any  max range
                    let latest_var = var.latest_version(self);
                    if matches!(
                        latest_var.underlying(self).into_expr_err(*loc)?.storage,
                        Some(StorageLocation::Memory(_))
                    ) {
                        let res = latest_var.ty(self).into_expr_err(*loc)?;
                        if let Some(r) = res.default_range(self).unwrap() {
                            let new_var = self.advance_var_in_ctx(latest_var, *loc, ctx).unwrap();
                            let res = new_var.set_range_min(self, r.min).into_expr_err(*loc);
                            let _ = self.add_if_err(res);
                            let res = new_var.set_range_max(self, r.max).into_expr_err(*loc);
                            let _ = self.add_if_err(res);
                        }
                    }
                    Ok(())
                })?;
                Ok(ExprRet::Multi(vec![]))
            }
            "sstore" => {
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about storage variables anymore.
                // We should check if the location is a reference to an existing var and update based on that
                let vars = ctx.local_vars(self);
                vars.iter().try_for_each(|var| {
                    // widen to any  max range
                    let latest_var = var.latest_version(self);
                    if matches!(
                        latest_var.underlying(self).into_expr_err(*loc)?.storage,
                        Some(StorageLocation::Storage(_))
                    ) {
                        let res = latest_var.ty(self).into_expr_err(*loc)?;
                        if let Some(r) = res.default_range(self).unwrap() {
                            let new_var = self.advance_var_in_ctx(latest_var, *loc, ctx).unwrap();
                            let res = new_var.set_range_min(self, r.min).into_expr_err(*loc);
                            let _ = self.add_if_err(res);
                            let res = new_var.set_range_max(self, r.max).into_expr_err(*loc);
                            let _ = self.add_if_err(res);
                        }
                    }
                    Ok(())
                })?;
                Ok(ExprRet::Multi(vec![]))
            }
            "not" => Err(ExprErr::Todo(
                *loc,
                format!("Unhandled builtin yul function: {id:?}"),
            )),

            _ => Err(ExprErr::Todo(
                *loc,
                format!("Unhandled builtin yul function: {id:?}"),
            )),
        }
    }

    fn return_yul(&mut self, loc: Loc, size: ExprRet) -> Result<(), ExprErr> {
        match size {
            ExprRet::CtxKilled => Ok(()),
            ExprRet::Single((ctx, size)) | ExprRet::SingleLiteral((ctx, size)) => {
                let b = Builtin::DynamicBytes;
                let mut var =
                    ContextVar::new_from_builtin(loc, self.builtin_or_add(b.clone()).into(), self)
                        .into_expr_err(loc)?;
                let mut range = SolcRange::try_from_builtin(&b).unwrap();
                match &mut range.min {
                    Elem::ConcreteDyn(ref mut r) => r.set_len(Elem::Dynamic(Dynamic::new(size))),
                    _ => unreachable!(),
                }
                match range.max {
                    Elem::ConcreteDyn(ref mut r) => r.set_len(Elem::Dynamic(Dynamic::new(size))),
                    _ => unreachable!(),
                }
                var.is_return = true;
                var.ty.set_range(range).into_expr_err(loc)?;
                let node = self.add_node(Node::ContextVar(var));
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Return));
                ctx.add_return_node(loc, ContextVarNode::from(node).latest_version(self), self)
                    .into_expr_err(loc)
            }
            ExprRet::Multi(sizes) => {
                sizes
                    .into_iter()
                    .try_for_each(|size| self.return_yul(loc, size))?;
                Ok(())
            }
            ExprRet::Fork(w1, w2) => {
                self.return_yul(loc, *w1)?;
                self.return_yul(loc, *w2)?;
                Ok(())
            }
        }
    }

    // fn byte_index(&mut self, var: ExprRet, index: ExprRet) -> Result<ExprRet, ExprErr> {
    //     match (var, index) {
    //         (ExprRet::Single((ctx, var_idx))
    //          | ExprRet::Single((ctx, var_idx)),
    //          ExprRet::Single((_, index_idx))
    //          | ExprRet::Single((_, index_idx)),
    //         ) => {

    //         }
    //     }
    // }
}