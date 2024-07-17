use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> MsgCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling msg-based intrinsic functions, like `gasleft`
pub trait MsgCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a msg's builtin function call, like `gasleft()`
    fn msg_call(&mut self, ctx: ContextNode, func_name: &str, loc: Loc) -> Result<(), ExprErr> {
        match &*func_name {
            "gasleft" => {
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Uint(64)).into(),
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
                    "Could not find builtin msg function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
