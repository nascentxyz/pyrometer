use crate::{
    context::exprs::{member_access::MemberAccess, require::Require},
    Builtin, ContextBuilder, Edge, ExprRet, Node, VarType,
};
use shared::{analyzer::AnalyzerLike, context::*, range::elem::RangeOp};

use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerLike<Expr = Expression> + Sized {}
pub trait Array: AnalyzerLike<Expr = Expression> + Sized {
    /// Gets the array type
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> ExprRet {
        let (ctx, inner_ty) = self.parse_ctx_expr(ty_expr, ctx).expect_single();
        if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
            let dyn_b = Builtin::Array(var_type);
            if let Some(idx) = self.builtins().get(&dyn_b) {
                ExprRet::Single((ctx, *idx))
            } else {
                let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                self.builtins_mut().insert(dyn_b, idx);
                ExprRet::Single((ctx, idx))
            }
        } else {
            panic!("Expected to be able to convert to a var type from an index to determine array type. This is a bug. Please report it at github.com/nascentxyz/pyrometer.")
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
        // println!("index into array");
        match (inner_paths, index_paths) {
            (_, ExprRet::CtxKilled) => ExprRet::CtxKilled,
            (ExprRet::CtxKilled, _) => ExprRet::CtxKilled,
            (ExprRet::Single((ctx, parent)), ExprRet::Single((_rhs_ctx, index))) | (ExprRet::Single((ctx, parent)), ExprRet::SingleLiteral((_rhs_ctx, index))) => {
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

                let name = format!("{}[{}]", parent.name(self), index.name(self));
                if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name) {
                    let index_var = index_var.latest_version(self);
                    let index_var = self.advance_var_in_ctx(index_var, loc, ctx);
                    ExprRet::Single((ctx, index_var.into()))
                } else {
                    let index_var = ContextVar {
                        loc: Some(loc),
                        name: name.clone(),
                        display_name: format!(
                            "{}[{}]",
                            parent.display_name(self),
                            index.display_name(self)
                        ),
                        storage: parent.storage(self).clone(),
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        ty: parent.ty(self).clone().array_underlying_ty(self),
                    };

                    let idx_node = self.add_node(Node::ContextVar(index_var));
                    self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                    self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(index, idx_node, Edge::Context(ContextEdge::Index));

                    ExprRet::Single((ctx, idx_node))
                }
            }
            e => panic!("Expected single expr evaluation of index expression, but was: {e:?}. This is a bug. Please report it at github.com/nascentxyz/pyrometer."),
        }
    }
}
