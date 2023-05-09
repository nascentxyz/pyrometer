use crate::context::exprs::IntoExprErr;
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use shared::{analyzer::AnalyzerLike, context::*, nodes::*, Edge, Node};
use solang_parser::pt::Expression;

use solang_parser::pt::{Parameter, ParameterList};

use solang_parser::pt::Loc;

impl<T> List for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}

pub trait List: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn list(&mut self, ctx: ContextNode, loc: Loc, params: &ParameterList) -> Result<(), ExprErr> {
        params
            .iter()
            .filter_map(|(_loc, input)| {
                if let Some(input) = input {
                    Some(input)
                } else {
                    None
                }
            }).try_for_each(|input| {
                self.parse_ctx_expr(&input.ty, ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "List did not have left hand sides".to_string()));
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    ctx.push_lhs_expr(analyzer.match_ty(ctx, &loc, &ret, input)?, analyzer).into_expr_err(loc)
                })
            })?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_lhs_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "List did not have left hand sides".to_string()));
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
            ExprRet::Single(ty) | ExprRet::SingleLiteral(ty) => {
                if let Some(input_name) = &input.name {
                    let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                    let var = ContextVar {
                        loc: Some(*loc),
                        name: input_name.to_string(),
                        display_name: input_name.to_string(),
                        storage: input.storage.clone(),
                        is_tmp: false,
                        is_symbolic: false,
                        tmp_of: None,
                        is_return: false,
                        ty,
                    };
                    let input_node = self.add_node(Node::ContextVar(var));
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
                                storage: input.storage.clone(),
                                is_tmp: true,
                                is_symbolic: false,
                                tmp_of: None,
                                is_return: false,
                                ty,
                            };
                            let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
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
