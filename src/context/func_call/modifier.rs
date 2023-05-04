use crate::context::exprs::IntoExprErr;
use crate::context::func_call::FuncCaller;

use crate::context::ExprErr;


use shared::analyzer::GraphLike;
use shared::context::*;

use solang_parser::pt::{Expression, Loc};

use shared::{analyzer::AnalyzerLike, nodes::*};

impl<T> ModifierCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
}
pub trait ModifierCaller:
    GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized
{
    fn handle_modifiers(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        _input_paths: &ExprRet,
        func: FunctionNode,
        _func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        if !func.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(func, ctx)?;
        }

        todo!()
    }
}
