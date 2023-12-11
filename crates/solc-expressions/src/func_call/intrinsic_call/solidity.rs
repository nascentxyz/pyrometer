use crate::{require::Require, ContextBuilder, ExprErr, func_call::helper::CallerHelper, IntoExprErr, ExpressionParser};

use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> SolidityCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper {}

/// Trait for calling solidity's intrinsic functions, like `keccak256`
pub trait SolidityCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper {
    /// Perform a solidity intrinsic function call, like `keccak256`
    fn solidity_call(
        &mut self,
        func_name: String,
        input_exprs: &[Expression],
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "keccak256" => {
                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(_input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "keccak256 call was not given inputs".to_string(),
                        ));
                    };
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
            "addmod" => {
                // TODO: actually calcuate this if possible
                self.parse_inputs(ctx, loc, input_exprs)?;

                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                    let var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            "mulmod" => {
                // TODO: actually calcuate this if possible
                self.parse_inputs(ctx, loc, input_exprs)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                    let var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            "require" | "assert" => self.apply_to_edges(ctx, loc, &|analyzer, ctx, _loc| {
                analyzer.handle_require(input_exprs, ctx)
            }),
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin solidity function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
