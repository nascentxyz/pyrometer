use crate::context::exprs::BinOp;
use crate::context::exprs::Cmp;
use crate::context::exprs::IntoExprErr;
use crate::context::yul::YulBuilder;
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use crate::Concrete;
use crate::ConcreteNode;
use crate::Node;
use ethers_core::types::U256;
use shared::analyzer::AnalyzerLike;
use shared::analyzer::GraphLike;
use shared::context::ExprRet;
use shared::range::elem_ty::RangeExpr;

use solang_parser::pt::YulExpression;
use std::cell::RefCell;
use std::rc::Rc;

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
    ) -> Result<(), ExprErr> {
        let YulFunctionCall { loc, id, arguments } = func_call;

        match &*id.name {
            "chainid" => {
                let b = Builtin::Uint(64);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "log0" | "log1" | "log2" | "log3" | "log4" => {
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "stop" | "revert" | "selfdestruct" | "invalid" => {
                ctx.kill(self, *loc, KilledKind::Revert).into_expr_err(*loc)
            }
            "return" => {
                self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(offset) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul Return had no offset".to_string()))
                    };
                    if matches!(offset, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(offset, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.parse_ctx_yul_expr(&arguments[1], ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(size) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Yul Return had no size".to_string()))
                        };
                        if matches!(size, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(size, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.return_yul(ctx, loc, size)?;
                        ctx.kill(analyzer, loc, KilledKind::Ended)
                            .into_expr_err(loc)?;
                        // ctx.push_expr(ExprRet::CtxKilled(KilledKind::Ended), analyzer)
                        //     .into_expr_err(loc)?;
                        Ok(())
                    })
                })
            }
            "not" => {
                if arguments.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        *loc,
                        format!(
                            "Yul function: `not` expected 1 argument found: {:?}",
                            arguments.len()
                        ),
                    ));
                }

                self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Not operation had no element".to_string()))
                    };

                    if matches!(lhs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.bit_not_inner(ctx, loc, lhs.flatten())
                })
            }
            "add" | "sub" | "mul" | "div" | "sdiv" | "mod" | "smod" | "exp" | "and" | "or"
            | "xor" | "shl" | "shr" | "sar" => {
                let op = match &*id.name {
                    "add" => RangeOp::Add(true),
                    "sub" => RangeOp::Sub(true),
                    "mul" => RangeOp::Mul(true),
                    "div" | "sdiv" => RangeOp::Div(true),
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

                let inputs: Vec<YulExpression> = if matches!(&*id.name, "shl" | "shr" | "sar") {
                    // yul shifts are super dumb and are reversed.
                    vec![arguments[1].clone(), arguments[0].clone()]
                } else {
                    vec![arguments[0].clone(), arguments[1].clone()]
                };

                self.parse_inputs(ctx, *loc, &inputs)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul Binary operation had no inputs".to_string()))
                    };
                    if matches!(inputs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    inputs.expect_length(2).into_expr_err(loc)?;
                    let inputs = inputs.as_vec();

                    let lhs_paths = &inputs[0];
                    let rhs_paths = &inputs[1];
                    analyzer.op_match(ctx, loc, lhs_paths, rhs_paths, op, false)
                })
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

                self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul Binary operation had no right hand side".to_string()))
                    };

                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    analyzer.parse_ctx_yul_expr(&arguments[1], ctx)?;
                    analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Yul Binary operation had no left hand side".to_string()))
                        };

                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.cmp_inner(ctx, loc, &lhs_paths, op, &rhs_paths)?;
                        let Some(result) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Yul Binary operation had no return".to_string()))
                        };

                        let res = ContextVarNode::from(result.expect_single().into_expr_err(loc)?);
                        let next = analyzer.advance_var_in_ctx(res, loc, ctx)?;
                        let expr = Elem::Expr(RangeExpr::new(
                            Elem::from(res),
                            RangeOp::Cast,
                            Elem::from(Concrete::Uint(1, U256::zero()))
                        ));

                        next.set_range_min(analyzer, expr.clone()).into_expr_err(loc)?;
                        next.set_range_max(analyzer, expr).into_expr_err(loc)?;
                        ctx.push_expr(
                            ExprRet::Single(next.into()),
                            analyzer,
                        )
                        .into_expr_err(loc)
                    })
                })
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

                self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul `iszero` operation had no input".to_string()))
                    };
                    if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    let cnode = ConcreteNode::from(
                        analyzer.add_node(Node::Concrete(Concrete::from(U256::from(0)))),
                    );
                    let tmp_true = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, analyzer)
                            .into_expr_err(loc)?,
                    );
                    let rhs_paths =
                        ExprRet::Single(ContextVarNode::from(analyzer.add_node(tmp_true)).into());

                    analyzer.cmp_inner(ctx, loc, &lhs_paths, RangeOp::Eq, &rhs_paths)
                })
            }
            "addmod" | "mulmod" => {
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "msize" | "pc" | "mload" | "sload" | "gas" | "returndatasize" => {
                // TODO: actually handle this. @MemoryModel
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "calldatacopy" => {
                // TODO: actually handle this. @MemoryModel
                Ok(())
            }
            "calldataload" => {
                if arguments.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        *loc,
                        format!(
                            "Yul function: `calldataload` expects 1 arguments found: {:?}",
                            arguments.len()
                        ),
                    ));
                }

                self.parse_ctx_yul_expr(&arguments[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Yul `calldataload` operation had no input".to_string()))
                    };
                    // TODO: check const version
                    let b = Builtin::Uint(256);
                    let mut var = ContextVar::new_from_builtin(loc, analyzer.builtin_or_add(b).into(), analyzer)
                        .into_expr_err(loc)?;
                    let elem = ContextVarNode::from(lhs_paths.expect_single().into_expr_err(loc)?);
                    var.display_name = format!("calldata[{}:{}+32]", elem.display_name(analyzer).into_expr_err(loc)?, elem.display_name(analyzer).into_expr_err(loc)?);
                    let node = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(node), analyzer)
                        .into_expr_err(loc)
                })
            }
            "keccak256" => {
                let b = Builtin::Bytes(32);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
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
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "create" | "create2" => {
                let b = Builtin::Address;
                let mut var =
                    ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                        .into_expr_err(*loc)?;
                var.display_name = format!("{id}_success");
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "returndatacopy" => {
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "byte" => {
                let b = Builtin::Uint(8);
                let var = ContextVar::new_from_builtin(*loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(*loc)?;
                let node = self.add_node(Node::ContextVar(var));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "mstore" | "mstore8" => {
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about memory variables anymore.
                // We should check if the location is a reference to an existing var and update based on that
                // @MemoryModel
                let vars = ctx.local_vars(self).clone();
                vars.into_iter().try_for_each(|(_name, var)| {
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
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            "sstore" => {
                // TODO: improve this. Right now we are extremely pessimistic and just say we know nothing about storage variables anymore.
                // We should check if the location is a reference to an existing var and update based on that
                let vars = ctx.local_vars(self).clone();
                vars.iter().try_for_each(|(_name, var)| {
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
                ctx.push_expr(ExprRet::Multi(vec![]), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            _ => Err(ExprErr::Todo(
                *loc,
                format!("Unhandled builtin yul function: {id:?}"),
            )),
        }
    }

    fn return_yul(&mut self, ctx: ContextNode, loc: Loc, size: ExprRet) -> Result<(), ExprErr> {
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
                let node = self.add_node(Node::ContextVar(var));
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Return));
                ctx.add_return_node(loc, ContextVarNode::from(node).latest_version(self), self)
                    .into_expr_err(loc)
            }
            ExprRet::Multi(sizes) => {
                sizes
                    .into_iter()
                    .try_for_each(|size| self.return_yul(ctx, loc, size))?;
                Ok(())
            }
            ExprRet::Null => Ok(()),
        }
    }

    // fn byte_index(&mut self, var: ExprRet, index: ExprRet) -> Result<ExprRet, ExprErr> {
    //     match (var, index) {
    //         (ExprRet::Single(var_idx)
    //          | ExprRet::Single(var_idx),
    //          ExprRet::Single(index_idx)
    //          | ExprRet::Single(index_idx),
    //         ) => {

    //         }
    //     }
    // }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_inputs(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        inputs: &[YulExpression],
    ) -> Result<(), ExprErr> {
        let append = if ctx.underlying(self).into_expr_err(loc)?.tmp_expr.is_empty() {
            Rc::new(RefCell::new(true))
        } else {
            Rc::new(RefCell::new(false))
        };

        inputs
            .iter()
            .try_for_each(|input| {
                self.parse_ctx_yul_expr(input, ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Inputs did not have left hand sides".to_string()));
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    if *append.borrow() {
                        ctx.append_tmp_expr(ret, analyzer).into_expr_err(loc)
                    } else {
                        *append.borrow_mut() = true;
                        ctx.push_tmp_expr(ret, analyzer).into_expr_err(loc)
                    }
                })
            })?;
        if !inputs.is_empty() {
            self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_tmp_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "Inputs did not have left hand sides".to_string()));
                };
                ctx.push_expr(ret, analyzer).into_expr_err(loc)
            })
        } else {
            Ok(())
        }
    }
}
