use crate::{
    AnalyzerLike, ContextBuilder, ContextEdge, ContextNode, ContextVar, ContextVarNode, DynBuiltin,
    Edge, Node, NodeIdx, VarType,
};

use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerLike + Sized {}
pub trait Array: AnalyzerLike + Sized {
    /// Gets the array type
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> Vec<NodeIdx> {
        let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
        if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
            let dyn_b = DynBuiltin::Array(var_type);
            if let Some(idx) = self.dyn_builtins().get(&dyn_b) {
                vec![*idx]
            } else {
                let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                self.dyn_builtins_mut().insert(dyn_b, idx);
                vec![idx]
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
    ) -> Vec<NodeIdx> {
        let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
        let index_ty = self.parse_ctx_expr(&index_expr, ctx)[0];

        let index_var = ContextVar {
            loc: Some(loc),
            name: ContextVarNode::from(index_ty).name(self),
            display_name: ContextVarNode::from(index_ty).display_name(self),
            storage: ContextVarNode::from(inner_ty).storage(self).clone(),
            tmp_of: None,
            ty: ContextVarNode::from(inner_ty)
                .ty(self)
                .array_underlying_ty(self),
        };

        let cvar_idx = self.add_node(Node::ContextVar(index_var));
        self.add_edge(cvar_idx, inner_ty, Edge::Context(ContextEdge::IndexAccess));

        self.add_edge(index_ty, cvar_idx, Edge::Context(ContextEdge::Index));

        vec![cvar_idx]
    }
}
