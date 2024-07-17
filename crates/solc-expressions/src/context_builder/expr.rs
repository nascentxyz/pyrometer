use crate::ExprTyParser;

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, KilledKind},
    AnalyzerBackend,
};
use shared::{post_to_site, ExprErr, IntoExprErr, RangeArena, USE_DEBUG_SITE};

use solang_parser::{helpers::CodeLocation, pt::Expression};

impl<T> ExpressionParser for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
}

/// Solidity expression parser
pub trait ExpressionParser:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
    /// Perform setup for parsing an expression
    fn parse_ctx_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        unreachable!("dead");
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self).replace('.', "\n\t.")))]
    /// Perform parsing of an expression
    fn parse_ctx_expr_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        unreachable!("dead");
    }
}
