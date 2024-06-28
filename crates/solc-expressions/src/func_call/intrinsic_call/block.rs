use crate::func_caller::NamedOrUnnamedArgs;
use crate::ContextBuilder;

use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, Node,
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
        func_name: String,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "blockhash" => {
                input_exprs.parse_n(arena, 1, self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, arena, &|analyzer, _arena, ctx, loc| {
                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "blockhash function was not provided a block number".to_string(),
                        ));
                    };
                    if matches!(input, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
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
