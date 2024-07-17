use crate::{ExpressionParser, TestCommandRunner};

use graph::{elem::Elem, nodes::Concrete, AnalyzerBackend};
use shared::{ExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Statement};

impl<T> StatementParser for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser
{
}

/// Solidity statement parser
pub trait StatementParser:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser + TestCommandRunner
{
    /// Performs setup for parsing a solidity statement
    fn parse_ctx_statement(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Copy>,
    ) where
        Self: Sized,
    {
        panic!("here");
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Performs parsing of a solidity statement
    fn parse_ctx_stmt_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Copy>,
    ) where
        Self: Sized,
    {
        panic!("here");
    }
}
