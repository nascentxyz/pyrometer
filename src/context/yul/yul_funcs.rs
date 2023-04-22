use crate::context::exprs::BinOp;
use crate::context::exprs::Cmp;
use crate::context::exprs::IntoExprErr;
use crate::context::yul::YulBuilder;
use crate::context::ExprErr;
use crate::Concrete;
use crate::ConcreteNode;
use crate::ExprRet;
use crate::Node;
use ethers_core::types::U256;
use shared::analyzer::AnalyzerLike;
use shared::analyzer::GraphLike;
use shared::{context::*, range::elem::RangeOp};
use solang_parser::pt::YulFunctionCall;
use solang_parser::pt::{Expression, Loc};

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
                    ContextVar::new_from_concrete(Loc::Implicit, cnode, self)
                        .into_expr_err(*loc)?,
                );
                let rhs_paths =
                    ExprRet::Single((ctx, ContextVarNode::from(self.add_node(tmp_true)).into()));

                self.cmp_inner(*loc, &lhs_paths, RangeOp::Eq, &rhs_paths)
            }
            _ => Err(ExprErr::Todo(
                *loc,
                format!("Unhandled builtin yul function: {id:?}"),
            )), // "stop" => {}
                // "stop" => {}
                // "stop" => {}
                // "stop" => {}
                // "stop" => {}
                // "stop" => {}
                // "stop" => {}
        }
    }
}
