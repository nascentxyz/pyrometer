use crate::ExprRet;
use crate::{
    AnalyzerLike, ContextBuilder, ContextEdge, ContextNode, ContextVar, ContextVarNode, DynBuiltin,
    Edge, Node, NodeIdx, VarType,
};

use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerLike + Sized {}
pub trait Array: AnalyzerLike + Sized {
    /// Gets the array type
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let (ctx, inner_ty) = self.parse_ctx_expr(&ty_expr, ctx).expect_single();
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
        let inner_tys = self.parse_ctx_expr(&ty_expr, ctx);
        let index_tys = self.parse_ctx_expr(&index_expr, ctx);
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
            (ExprRet::Single((lhs_ctx, inner_ty)), ExprRet::Single((_rhs_ctx, index_ty))) => {
                let index_var = ContextVar {
                    loc: Some(loc),
                    name: ContextVarNode::from(index_ty).name(self),
                    display_name: ContextVarNode::from(index_ty).display_name(self),
                    storage: ContextVarNode::from(index_ty).storage(self).clone(),
                    is_tmp: ContextVarNode::from(index_ty).is_tmp(self),
                    tmp_of: None,
                    ty: ContextVarNode::from(inner_ty)
                        .ty(self)
                        .array_underlying_ty(self),
                };

                let cvar_idx = self.add_node(Node::ContextVar(index_var));
                self.add_edge(cvar_idx, inner_ty, Edge::Context(ContextEdge::IndexAccess));

                self.add_edge(index_ty, cvar_idx, Edge::Context(ContextEdge::Index));

                ExprRet::Single((lhs_ctx, cvar_idx))
            }
            _ => todo!("here")
        }
    }
}
