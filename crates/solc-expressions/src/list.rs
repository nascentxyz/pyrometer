use crate::{ContextBuilder, ExprErr, IntoExprErr, ExpressionParser};

use graph::{
    nodes::{ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};

use solang_parser::pt::{Expression, Loc, Parameter, ParameterList};

impl<T> List for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Dealing with list parsing and operations
pub trait List: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn list(&mut self, ctx: ContextNode, loc: Loc, params: &ParameterList) -> Result<(), ExprErr> {
        params.iter().try_for_each(|(loc, input)| {
            if let Some(input) = input {
                self.parse_ctx_expr(&input.ty, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "List did not have left hand sides".to_string(),
                        ));
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    ctx.append_tmp_expr(analyzer.match_ty(ctx, &loc, &ret, input)?, analyzer)
                        .into_expr_err(loc)
                })
            } else {
                // create a dummy var
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    ctx.append_tmp_expr(ExprRet::Null, analyzer)
                        .into_expr_err(loc)
                })
            }
        })?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_tmp_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(
                    loc,
                    "List did not have left hand sides".to_string(),
                ));
            };
            ctx.push_expr(ret, analyzer).into_expr_err(loc)
        })
    }

    fn match_ty(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        ty_ret: &ExprRet,
        input: &Parameter,
    ) -> Result<ExprRet, ExprErr> {
        match ty_ret {
            ExprRet::Null => Ok(ExprRet::Null),
            ExprRet::Single(ty) | ExprRet::SingleLiteral(ty) => {
                if let Some(input_name) = &input.name {
                    let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                    let var = ContextVar {
                        loc: Some(*loc),
                        name: input_name.to_string(),
                        display_name: input_name.to_string(),
                        storage: input.storage.as_ref().map(|s| s.clone().into()),
                        is_tmp: false,
                        is_symbolic: false,
                        tmp_of: None,
                        is_return: false,
                        ty,
                    };
                    let input_node = self.add_node(Node::ContextVar(var));
                    ctx.add_var(input_node.into(), self).into_expr_err(*loc)?;
                    self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(input_node))
                } else {
                    match self.node(*ty) {
                        Node::ContextVar(_var) => {
                            // reference the variable directly, don't create a temporary variable
                            Ok(ExprRet::Single(*ty))
                        }
                        _ => {
                            // create a tmp
                            let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                            let tmp_num = ctx.new_tmp(self).into_expr_err(*loc)?;
                            let new_lhs_underlying = ContextVar {
                                loc: Some(*loc),
                                name: format!("tmp{tmp_num}"),
                                display_name: format!("tmp{tmp_num}"),
                                storage: input.storage.as_ref().map(|s| s.clone().into()),
                                is_tmp: true,
                                is_symbolic: false,
                                tmp_of: None,
                                is_return: false,
                                ty,
                            };
                            let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
                            ctx.add_var(input_node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(input_node))
                        }
                    }
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .iter()
                    .map(|i| self.match_ty(ctx, loc, i, input))
                    .collect::<Result<_, _>>()?,
            )),
            ExprRet::CtxKilled(kind) => Ok(ExprRet::CtxKilled(*kind)),
        }
    }
}
