use crate::{
    IntoExprErr, ExprErr, FuncCaller
};

use graph::{
    GraphBackend, AnalyzerBackend,
    nodes::{FunctionNode, ContextNode, ExprRet, }
};

use solang_parser::pt::{Expression, Loc};

impl<T> ModifierCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}
pub trait ModifierCaller:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
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