use crate::context::exprs::member_access::MemberAccess;
use crate::context::exprs::require::Require;
use crate::ExprRet;
use crate::{ContextBuilder, DynBuiltin, Edge, Node, VarType};
use petgraph::{visit::EdgeRef, Direction};
use shared::analyzer::AnalyzerLike;
use shared::context::*;
use shared::range::elem::RangeOp;

use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerLike + Sized {}
pub trait Array: AnalyzerLike + Sized {
    /// Gets the array type
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let (ctx, inner_ty) = self.parse_ctx_expr(ty_expr, ctx).expect_single();
        if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
            let dyn_b = DynBuiltin::Array(var_type);
            if let Some(idx) = self.dyn_builtins().get(&dyn_b) {
                ExprRet::Single((ctx, *idx))
            } else {
                let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                self.dyn_builtins_mut().insert(dyn_b, idx);
                ExprRet::Single((ctx, idx))
            }
        } else {
            todo!("???")
        }
    }

    /// Indexes into an array
    fn index_into_array(
        &mut self,
        loc: Loc,
        ty_expr: &Expression,
        index_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let inner_tys = self.parse_ctx_expr(ty_expr, ctx);
        let index_tys = self.parse_ctx_expr(index_expr, ctx);
        self.index_into_array_inner(loc, inner_tys, index_tys)
    }

    fn index_into_array_inner(
        &mut self,
        loc: Loc,
        inner_paths: ExprRet,
        index_paths: ExprRet,
    ) -> ExprRet {
        match (inner_paths, index_paths) {
            (_, ExprRet::CtxKilled) => ExprRet::CtxKilled,
            (ExprRet::CtxKilled, _) => ExprRet::CtxKilled,
            (ExprRet::Single((ctx, parent)), ExprRet::Single((_rhs_ctx, index))) => {
                let index = ContextVarNode::from(index);
                let parent = ContextVarNode::from(parent).first_version(self);
                let len_var = self.tmp_length(parent, ctx, loc);
                let idx = self.advance_var_in_ctx(index, loc, ctx);
                self.handle_require_inner(
                    loc,
                    &ExprRet::Single((ctx, idx.into())),
                    &ExprRet::Single((ctx, len_var.into())),
                    RangeOp::Lt,
                    RangeOp::Gt,
                    (RangeOp::Gte, RangeOp::Lte),
                );
                if let Some(idx_var) = self
                    .graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::IndexAccess))
                    .map(|edge| ContextVarNode::from(edge.source()))
                    .filter(|cvar| {
                        cvar.name(self) == format!("{}[{}]", parent.name(self), index.name(self))
                    })
                    .take(1)
                    .next()
                {
                    let idx_var = idx_var.latest_version(self);
                    let new_idx = self.advance_var_in_ctx(idx_var, loc, ctx);

                    ExprRet::Single((ctx, new_idx.into()))
                } else {
                    let index_var = ContextVar {
                        loc: Some(loc),
                        name: format!("{}[{}]", parent.name(self), index.name(self)),
                        display_name: format!(
                            "{}[{}]",
                            parent.display_name(self),
                            index.display_name(self)
                        ),
                        storage: parent.storage(self).clone(),
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        ty: parent.ty(self).array_underlying_ty(self),
                    };

                    let idx_node = self.add_node(Node::ContextVar(index_var));
                    self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                    self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));

                    ExprRet::Single((ctx, idx_node))
                }
            }
            _ => todo!("here"),
        }
    }
}
