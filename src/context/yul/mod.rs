use solang_parser::pt::{YulExpression, YulStatement};

mod yul_cond_op;
pub use yul_cond_op::*;

impl<T> YulBuilder for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser {}
pub trait YulBuilder:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
	fn parse_ctx_yul_statement(
        &mut self,
        stmt: &YulStatement,
        ctx: ContextNode,
    ) where
        Self: Sized,
    {
        if let Some(true) =
            self.add_if_err(ctx.is_ended(self).into_expr_err(stmt.loc()))
        {
            return;
        }
        if let Some(live_forks) =
            self.add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
        {
            if live_forks.is_empty() {
                self.parse_ctx_yul_stmt_inner(stmt, ctx)
            } else {
                live_forks.iter().for_each(|fork_ctx| {
                    self.parse_ctx_yul_stmt_inner(stmt, *fork_ctx);
                });
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_yul_stmt_inner(
        &mut self,
        stmt: &YulStatement,
        ctx: ContextNode,
    ) where
        Self: Sized,
    {
    	use YulStatement::*;
    	let forks = self
                    .add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
                    .unwrap();
    	match stmt {
		    Assign(loc, yul_exprs, yul_expr) => {
		    	if forks.is_empty() {
			    	if let Some(lhs_side) = self.add_if_err(yul_exprs.iter().map(|expr| {
			    		self.parse_ctx_yul_expr(expr, ctx)
			    	}).collect::<Result<Vec<ExprRet>, ExprErr>>()) {
			    		if let Some(rhs_side) = self.add_if_err(self.parse_ctx_yul_expr(yul_expr, ctx)) {
			    			let _ = self.add_if_err(self.match_assign_sides(stmt.loc(), &ExprRet::Multi(lhs_side), rhs_side));
				    	}
			    	}
			    } else {
			    	forks.into_iter().for_each(|ctx| {
			    		if let Some(lhs_side) = self.add_if_err(yul_exprs.iter().map(|expr| {
				    		self.parse_ctx_yul_expr(expr, ctx)
				    	}).collect::<Result<Vec<ExprRet>, ExprErr>>()) {
				    		if let Some(rhs_side) = self.add_if_err(self.parse_ctx_yul_expr(yul_expr, ctx)) {
				    			let _ = self.add_if_err(self.match_assign_sides(stmt.loc(), &ExprRet::Multi(lhs_side), rhs_side));
					    	}
				    	}
			    	});
			    }
		    },
		    VariableDeclaration(loc, yul_idents, maybe_yul_expr) => {
		    
		    },
		    If(loc, yul_expr, yul_block) => {
		    	if forks.is_empty() {
			    	let _ = self.add_if_err(self.yul_cond_op_stmt(loc, yul_expr, yul_block, ctx));
			    } else {
			    	forks.into_iter().for_each(|ctx| {
			    		let _ = self.add_if_err(self.yul_cond_op_stmt(loc, yul_expr, yul_block, ctx));
			    	});
			    }
		    },
		    For(YulFor { loc, init_block, condition, post_block, execution_block }) => {
		    
		    },
		    Switch(YulSwitch { loc, condition, cases, default }) => {

		    },
		    Leave(loc) => {

		    },
		    Break(loc) => {

		    },
		    Continue(loc) => {

		    },
		    Block(yul_block) => {
		    	yul_block.statements.for_each(|stmt| {
		    		self.parse_ctx_yul_stmt_inner(stmt)
		    	});
		    },
		    FunctionDefinition(yul_func_def) => {
		    	
		    },
		    FunctionCall(yul_func_call) => {

		    },
		    Error(loc) => {

		    },
    	}
    }

    fn parse_ctx_yul_expr(&mut self, expr: &YulExpression, ctx: ContextNode) -> Result<ExprRet, ExprErr> {
        if ctx.is_ended(self).into_expr_err(expr.loc())? {
            return Ok(ExprRet::CtxKilled);
        }

        if ctx.live_forks(self).into_expr_err(expr.loc())?.is_empty() {
            self.parse_ctx_yul_expr_inner(expr, ctx)
        } else {
            let rets: Vec<ExprRet> = ctx
                .live_forks(self)
                .into_expr_err(expr.loc())?
                .iter()
                .map(|fork_ctx| self.parse_ctx_yul_expr(expr, *fork_ctx))
                .collect::<Result<_, ExprErr>>()?;
            if rets.len() == 1 {
                Ok(rets.into_iter().take(1).next().unwrap())
            } else {
                Ok(ExprRet::Multi(rets))
            }
        }
    }

    fn parse_ctx_yul_expr_inner(
        &mut self,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
    	use YulExpression::*;
    	match expr {
		    BoolLiteral(loc, b, _) => self.bool_literal(ctx, *loc, b),
		    NumberLiteral(loc, int, expr, _unit) => self.number_literal(ctx, *loc, int, exp, false),
		    HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
		    HexStringLiteral(lit, _) => self.hex_literals(ctx, [lit]),
		    StringLiteral(lit, _) => self.string_literal(ctx, lit.loc, &lit.string),
		    Variable(ident) => self.variable(ident, ctx),
		    FunctionCall(_) => Err(Todo(expr.loc(), "Yul function calls not yet supported")),
		    SuffixAccess(loc, yul_member_expr, ident) => Err(Todo(expr.loc(), "Yul member access not yet supported")),
    	}
    }
}