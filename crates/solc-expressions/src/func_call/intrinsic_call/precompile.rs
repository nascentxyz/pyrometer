use crate::{ContextBuilder, ExprErr, FuncCaller, IntoExprErr};

use graph::{
    nodes::{Builtin, Context, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Loc};

impl<T> PrecompileCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{}
pub trait PrecompileCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn precompile_call(
        &mut self,
        func_name: String,
        func_idx: NodeIdx,
        input_exprs: &[Expression],
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "sha256" => {
                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "abi.decode was not given the types for decoding".to_string(),
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
            "ripemd160" => {
                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "abi.decode was not given the types for decoding".to_string(),
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
            "ecrecover" => {
                self.parse_inputs(ctx, loc, input_exprs)?;

                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let cctx = Context::new_subctx(
                        ctx,
                        None,
                        loc,
                        None,
                        Some(func_idx.into()),
                        true,
                        analyzer,
                        None,
                    )
                    .into_expr_err(loc)?;
                    let call_ctx = analyzer.add_node(Node::Context(cctx));
                    ctx.set_child_call(call_ctx.into(), analyzer)
                        .into_expr_err(loc)?;
                    let call_node = analyzer.add_node(Node::FunctionCall);
                    analyzer.add_edge(call_node, func_idx, Edge::Context(ContextEdge::Call));
                    analyzer.add_edge(call_node, ctx, Edge::Context(ContextEdge::Subcontext));
                    analyzer.add_edge(call_ctx, call_node, Edge::Context(ContextEdge::Subcontext));

                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "ecrecover did not receive inputs".to_string(),
                        ));
                    };

                    if matches!(input, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    let mut inner_vals = vec![];
                    match input {
                        ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                            inner_vals
                                .push(ContextVarNode::from(var).display_name(analyzer).unwrap());
                        }
                        _ => inner_vals.push("<unknown>".to_string()),
                    }
                    let inner_name = inner_vals.into_iter().collect::<Vec<_>>().join(", ");
                    let mut var = ContextVar::new_from_builtin(
                        loc,
                        analyzer.builtin_or_add(Builtin::Address).into(),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    var.display_name = format!("ecrecover({})", inner_name);
                    var.is_symbolic = true;
                    var.is_return = true;
                    let cvar = analyzer.add_node(Node::ContextVar(var));
                    ctx.add_var(cvar.into(), analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Variable));
                    analyzer.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Return));
                    ContextNode::from(call_ctx)
                        .add_return_node(loc, cvar.into(), analyzer)
                        .into_expr_err(loc)?;

                    let rctx = Context::new_subctx(
                        call_ctx.into(),
                        Some(ctx),
                        loc,
                        None,
                        None,
                        true,
                        analyzer,
                        None,
                    )
                    .into_expr_err(loc)?;
                    let ret_ctx = analyzer.add_node(Node::Context(rctx));
                    ContextNode::from(call_ctx)
                        .set_child_call(ret_ctx.into(), analyzer)
                        .into_expr_err(loc)?;
                    analyzer.add_edge(ret_ctx, call_ctx, Edge::Context(ContextEdge::Continue));

                    let tmp_ret = ContextVarNode::from(cvar)
                        .as_tmp(
                            ContextNode::from(call_ctx)
                                .underlying(analyzer)
                                .unwrap()
                                .loc,
                            ret_ctx.into(),
                            analyzer,
                        )
                        .unwrap();
                    tmp_ret.underlying_mut(analyzer).unwrap().is_return = true;
                    tmp_ret.underlying_mut(analyzer).unwrap().display_name =
                        format!("ecrecover({}).return", inner_name);
                    ctx.add_var(tmp_ret, analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(tmp_ret, ret_ctx, Edge::Context(ContextEdge::Variable));

                    ContextNode::from(ret_ctx)
                        .push_expr(ExprRet::Single(tmp_ret.into()), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find precompile function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
