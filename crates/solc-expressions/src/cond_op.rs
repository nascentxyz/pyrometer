use crate::require::Require;

use graph::AnalyzerBackend;
use shared::ExprErr;

use solang_parser::pt::Expression;

impl<T> CondOp for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized
{}
/// Handles conditional operations, like `if .. else ..` and ternary operations
pub trait CondOp: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Require + Sized {}
