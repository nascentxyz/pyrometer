use crate::{context::ContextBuilder, ExprRet};
use shared::{analyzer::AnalyzerLike, context::*, nodes::*, Edge, Node};
use solang_parser::pt::Expression;

use solang_parser::pt::{Parameter, ParameterList};

use solang_parser::pt::Loc;

impl<T> List for T where T: AnalyzerLike<Expr = Expression> + Sized {}

pub trait List: AnalyzerLike<Expr = Expression> + Sized {
    fn list(&mut self, ctx: ContextNode, _loc: Loc, params: &ParameterList) -> ExprRet {
        let rets = params
            .iter()
            .filter_map(|(loc, input)| {
                if let Some(input) = input {
                    let ret = self.parse_ctx_expr(&input.ty, ctx);
                    Some(self.match_ty(loc, &ret, input))
                } else {
                    None
                }
            })
            .collect();
        ExprRet::Multi(rets).flatten()
    }

    fn match_ty(&mut self, loc: &Loc, ty_ret: &ExprRet, input: &Parameter) -> ExprRet {
        match ty_ret {
            ExprRet::Single((lhs_ctx, ty)) | ExprRet::SingleLiteral((lhs_ctx, ty)) => {
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
                        ty,
                    };
                    let input_node = self.add_node(Node::ContextVar(var));
                    self.add_edge(input_node, *lhs_ctx, Edge::Context(ContextEdge::Variable));
                    ExprRet::Single((*lhs_ctx, input_node))
                } else {
                    match self.node(*ty) {
                        Node::ContextVar(_var) => {
                            // reference the variable directly, don't create a temporary variable
                            ExprRet::Single((*lhs_ctx, *ty))
                        }
                        _ => {
                            // create a tmp
                            let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                            let tmp_num = lhs_ctx.new_tmp(self);
                            let new_lhs_underlying = ContextVar {
                                loc: Some(*loc),
                                name: format!("tmp{tmp_num}"),
                                display_name: format!("tmp{tmp_num}"),
                                storage: input.storage.clone(),
                                is_tmp: true,
                                is_symbolic: false,
                                tmp_of: None,
                                ty,
                            };
                            let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
                            self.add_edge(
                                input_node,
                                *lhs_ctx,
                                Edge::Context(ContextEdge::Variable),
                            );
                            ExprRet::Single((*lhs_ctx, input_node))
                        }
                    }
                }
            }
            ExprRet::Multi(inner) => {
                ExprRet::Multi(inner.iter().map(|i| self.match_ty(loc, i, input)).collect())
            }
            ExprRet::Fork(w1, w2) => ExprRet::Fork(
                Box::new(self.match_ty(loc, w1, input)),
                Box::new(self.match_ty(loc, w2, input)),
            ),
            ExprRet::CtxKilled => ExprRet::CtxKilled,
        }
    }
}
