use crate::context::ContextBuilder;
use crate::ContextNode;
use crate::Edge;
use crate::ExprRet;
use crate::VarType;
use crate::{AnalyzerLike, ContextEdge, ContextVar, Node};
use solang_parser::pt::ParameterList;

use solang_parser::pt::Loc;

impl<T> List for T where T: AnalyzerLike + Sized {}

pub trait List: AnalyzerLike + Sized {
    fn list(&mut self, ctx: ContextNode, _loc: Loc, params: &ParameterList) -> ExprRet {
        let rets = params
            .iter()
            .filter_map(|(loc, input)| {
                if let Some(input) = input {
                    if let Some(input_name) = &input.name {
                        let (lhs_ctx, ty) = self.parse_ctx_expr(&input.ty, ctx).expect_single();
                        let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                        let var = ContextVar {
                            loc: Some(*loc),
                            name: input_name.to_string(),
                            display_name: input_name.to_string(),
                            storage: input.storage.clone(),
                            is_tmp: false,
                            tmp_of: None,
                            ty,
                        };
                        let input_node = self.add_node(Node::ContextVar(var));
                        self.add_edge(input_node, lhs_ctx, Edge::Context(ContextEdge::Variable));
                        Some(ExprRet::Single((lhs_ctx, input_node)))
                    } else {
                        let (lhs_ctx, ty) = self.parse_ctx_expr(&input.ty, ctx).expect_single();
                        let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                        let tmp_num = ctx.new_tmp(self);
                        let new_lhs_underlying = ContextVar {
                            loc: Some(*loc),
                            name: format!("tmp{}", tmp_num),
                            display_name: format!("tmp{}", tmp_num),
                            storage: input.storage.clone(),
                            is_tmp: true,
                            tmp_of: None,
                            ty,
                        };
                        let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
                        self.add_edge(input_node, lhs_ctx, Edge::Context(ContextEdge::Variable));
                        Some(ExprRet::Single((lhs_ctx, input_node)))
                    }
                } else {
                    None
                }
            })
            .collect();
        ExprRet::Multi(rets)
    }
}
