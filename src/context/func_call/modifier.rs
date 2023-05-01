use crate::context::exprs::IntoExprErr;
use crate::context::func_call::FuncCaller;
use crate::context::func_call::{
    internal_call::InternalFuncCaller, intrinsic_call::IntrinsicFuncCaller,
    namespaced_call::NameSpaceFuncCaller,
};
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use crate::ExprRet;
use shared::analyzer::AsDotStr;
use shared::analyzer::GraphError;
use shared::analyzer::GraphLike;
use shared::context::*;
use std::collections::BTreeMap;

use shared::range::Range;
use solang_parser::pt::{Expression, Loc, NamedArgument, StorageLocation};

use crate::VarType;

use shared::{analyzer::AnalyzerLike, nodes::*, Edge, Node, NodeIdx};

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
        input_paths: &ExprRet,
        func: FunctionNode,
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        if !func.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(func, ctx)?;
        }

        todo!()
    }
}
