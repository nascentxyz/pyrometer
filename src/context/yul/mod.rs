
use solang_parser::pt::YulStatement;



pub trait YulBuilder:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
	fn parse_ctx_yul_statement(
        &mut self,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        if let Some(parent) = parent_ctx {
            match self.node(parent) {
                Node::Context(_) => {
                    let ctx = ContextNode::from(parent.into());
                    if let Some(true) =
                        self.add_if_err(ctx.is_ended(self).into_expr_err(stmt.loc()))
                    {
                        return;
                    }
                    if let Some(live_forks) =
                        self.add_if_err(ctx.live_forks(self).into_expr_err(stmt.loc()))
                    {
                        if live_forks.is_empty() {
                            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
                        } else {
                            live_forks.iter().for_each(|fork_ctx| {
                                self.parse_ctx_stmt_inner(stmt, unchecked, Some(*fork_ctx));
                            });
                        }
                    }
                }
                _ => self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx),
            }
        } else {
            // println!("function entry: {:?}", parent_ctx.map(|ctx| self.node(ctx.into())));
            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_yul_stmt_inner(
        &mut self,
        stmt: &Statement,
        _unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
    	use YulStatement::*;
    }

}