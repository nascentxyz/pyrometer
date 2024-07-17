use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

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
        match &*func_name {
            "blockhash" => {
                let input = inputs.expect_single().into_expr_err(loc)?;
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
