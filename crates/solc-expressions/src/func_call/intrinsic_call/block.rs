use crate::{
    ContextBuilder, ExprErr, IntoExprErr,
};

use graph::{
    nodes::{
        Builtin, ContextNode, ContextVar, ExprRet,
    },
    AnalyzerBackend, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> BlockCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait BlockCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn block_call(&mut self, func_name: String, input_exprs: &[Expression], loc: Loc, ctx: ContextNode) -> Result<(), ExprErr> {
    	match &*func_name {
			"blockhash" => {
			    self.parse_ctx_expr(&input_exprs[0], ctx)?;
			    self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
			        let Some(input) =
			            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
			        else {
			            return Err(ExprErr::NoRhs(
			                loc,
			                "blockhash function was not provided a block number"
			                    .to_string(),
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
	            )
	        ))
		}
	}
}