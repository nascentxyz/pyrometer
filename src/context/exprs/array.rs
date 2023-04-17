use crate::context::ExprErr;
use crate::context::IntoExprErr;
use crate::{
    context::exprs::{member_access::MemberAccess, require::Require},
    Builtin, ContextBuilder, Edge, ExprRet, Node, VarType,
};
use shared::{analyzer::AnalyzerLike, context::*, range::elem::RangeOp};
use solang_parser::helpers::CodeLocation;

use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait Array: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Gets the array type
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> Result<ExprRet, ExprErr> {
        let ret = self.parse_ctx_expr(ty_expr, ctx)?;
        self.match_ty(ty_expr, ret)
    }

    fn match_ty(&mut self, ty_expr: &Expression, ret: ExprRet) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Single((ctx, inner_ty)) | ExprRet::SingleLiteral((ctx, inner_ty)) => {
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = Builtin::Array(var_type);
                    if let Some(idx) = self.builtins().get(&dyn_b) {
                        Ok(ExprRet::Single((ctx, *idx)))
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins_mut().insert(dyn_b, idx);
                        Ok(ExprRet::Single((ctx, idx)))
                    }
                } else {
                    Err(ExprErr::ArrayTy(ty_expr.loc(), "Expected to be able to convert to a var type from an index to determine array type. This is a bug. Please report it at github.com/nascentxyz/pyrometer.".to_string()))
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|i| self.match_ty(ty_expr, i))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_ty(ty_expr, *w1)?),
                Box::new(self.match_ty(ty_expr, *w2)?),
            )),
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
        }
    }

    /// Indexes into an array
    fn index_into_array(
        &mut self,
        loc: Loc,
        ty_expr: &Expression,
        index_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let inner_tys = self.parse_ctx_expr(ty_expr, ctx)?;
        let index_tys = self.parse_ctx_expr(index_expr, ctx)?;
        self.index_into_array_inner(loc, inner_tys, index_tys)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn index_into_array_inner(
        &mut self,
        loc: Loc,
        inner_paths: ExprRet,
        index_paths: ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match (inner_paths, index_paths) {
            (_, ExprRet::CtxKilled) => Ok(ExprRet::CtxKilled),
            (ExprRet::CtxKilled, _) => Ok(ExprRet::CtxKilled),
            (ExprRet::Single((ctx, parent)), ExprRet::Single((_rhs_ctx, index))) | (ExprRet::Single((ctx, parent)), ExprRet::SingleLiteral((_rhs_ctx, index))) => {
                let index = ContextVarNode::from(index).latest_version(self);
                let parent = ContextVarNode::from(parent).first_version(self);
                let idx = self.advance_var_in_ctx(index, loc, ctx)?;
                if !parent.is_mapping(self).into_expr_err(loc)? {
                    let len_var = self.tmp_length(parent, ctx, loc).latest_version(self);
                    self.handle_require_inner(
                        loc,
                        &ExprRet::Single((ctx, len_var.latest_version(self).into())),
                        &ExprRet::Single((ctx, idx.latest_version(self).into())),
                        RangeOp::Gt,
                        RangeOp::Lt,
                        (RangeOp::Lte, RangeOp::Gte),
                    )?;
                }

                let name = format!("{}[{}]", parent.name(self).into_expr_err(loc)?, index.name(self).into_expr_err(loc)?);
                tracing::trace!("indexing: {}", name);

                if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
                    let index_var = index_var.latest_version(self);
                    let index_var = self.advance_var_in_ctx(index_var, loc, ctx)?;
                    Ok(ExprRet::Single((ctx, index_var.into())))
                } else {
                    let index_var = ContextVar {
                        loc: Some(loc),
                        name: name.clone(),
                        display_name: format!(
                            "{}[{}]",
                            parent.display_name(self).into_expr_err(loc)?,
                            index.display_name(self).into_expr_err(loc)?
                        ),
                        storage: parent.storage(self).into_expr_err(loc)?.clone(),
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        ty: parent.ty(self).into_expr_err(loc)?.clone().dynamic_underlying_ty(self).into_expr_err(loc)?,
                    };

                    let idx_node = self.add_node(Node::ContextVar(index_var));
                    self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                    self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                    self.add_edge(index, idx_node, Edge::Context(ContextEdge::Index));

                    Ok(ExprRet::Single((ctx, idx_node)))
                }
            }
            e => Err(ExprErr::ArrayIndex(loc, format!("Expected single expr evaluation of index expression, but was: {e:?}. This is a bug. Please report it at github.com/nascentxyz/pyrometer."))),
        }
    }
}
