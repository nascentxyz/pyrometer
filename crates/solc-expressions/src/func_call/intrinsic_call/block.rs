use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::H256;

use solang_parser::pt::{Expression, Loc};

impl<T> BlockCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling block-based intrinsic functions
pub trait BlockCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a `block` function call
    fn block_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match func_name {
            "blockhash" => {
                let _input = inputs.expect_single().into_expr_err(loc)?;
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Bytes(32)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "blobhash" => {
                let _input = inputs.expect_single().into_expr_err(loc)?;
                let mut var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Bytes(32)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let mut range = var.ty.take_range().unwrap();
                // https://docs.soliditylang.org/en/latest/units-and-global-variables.html#block-and-transaction-properties
                // we set the first byte to 0x01 per solidity docs
                let mut min = [0; 32];
                min[0] = 1;
                let mut max = [u8::MAX; 32];
                max[0] = 1;
                range.min = Elem::from(Concrete::Bytes(32, H256(min)));
                range.max = Elem::from(Concrete::Bytes(32, H256(max)));
                var.ty.set_range(range).into_expr_err(loc)?;
                let cvar = ContextVarNode::from(self.add_node(var));
                ctx.push_expr(ExprRet::Single(cvar.0.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin block function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
