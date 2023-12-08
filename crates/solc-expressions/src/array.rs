use crate::{member_access::MemberAccess, require::Require, ContextBuilder, ExprErr, IntoExprErr};

use graph::{
    elem::RangeOp,
    nodes::{Builtin, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};

use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Loc},
};

impl<T> Array for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait Array: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Gets the array type
    #[tracing::instrument(level = "trace", skip_all)]
    fn array_ty(&mut self, ty_expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        self.parse_ctx_expr(ty_expr, ctx)?;
        self.apply_to_edges(ctx, ty_expr.loc(), &|analyzer, ctx, loc| {
            if let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? {
                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                analyzer.match_ty(ctx, ty_expr, ret)
            } else {
                Err(ExprErr::NoLhs(
                    loc,
                    "No array specified for getting array type".to_string(),
                ))
            }
        })
    }

    fn match_ty(
        &mut self,
        ctx: ContextNode,
        ty_expr: &Expression,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(inner_ty) | ExprRet::SingleLiteral(inner_ty) => {
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = Builtin::Array(var_type);
                    if let Some(idx) = self.builtins().get(&dyn_b) {
                        ctx.push_expr(ExprRet::Single(*idx), self)
                            .into_expr_err(ty_expr.loc())?;
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins_mut().insert(dyn_b, idx);
                        ctx.push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(ty_expr.loc())?;
                    }
                    Ok(())
                } else {
                    Err(ExprErr::ArrayTy(ty_expr.loc(), "Expected to be able to convert to a var type from an index to determine array type. This is a bug. Please report it at github.com/nascentxyz/pyrometer.".to_string()))
                }
            }
            ExprRet::Multi(inner) => {
                inner
                    .into_iter()
                    .map(|i| self.match_ty(ctx, ty_expr, i))
                    .collect::<Result<Vec<_>, ExprErr>>()?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, ty_expr.loc(), kind)
                    .into_expr_err(ty_expr.loc())?;
                Ok(())
            }
            ExprRet::Null => Ok(()),
        }
    }

    /// Indexes into an array
    #[tracing::instrument(level = "trace", skip_all)]
    fn index_into_array(
        &mut self,
        loc: Loc,
        ty_expr: &Expression,
        index_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        tracing::trace!("Indexing into array");
        self.parse_ctx_expr(index_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(index_tys) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "Could not find the index variable".to_string(),
                ));
            };
            if matches!(index_tys, ExprRet::CtxKilled(_)) {
                ctx.push_expr(index_tys, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.parse_ctx_expr(ty_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(inner_tys) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "Could not find the array".to_string()));
                };
                if matches!(inner_tys, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(inner_tys, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                analyzer.index_into_array_inner(
                    ctx,
                    loc,
                    inner_tys.flatten(),
                    index_tys.clone().flatten(),
                )
            })
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn index_into_array_inner(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        inner_paths: ExprRet,
        index_paths: ExprRet,
    ) -> Result<(), ExprErr> {
        match (inner_paths, index_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (_, ExprRet::CtxKilled(kind)) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)
            }
            (ExprRet::CtxKilled(kind), _) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)
            }
            (ExprRet::Single(parent), ExprRet::Single(index)) | (ExprRet::Single(parent), ExprRet::SingleLiteral(index)) => {
                let index = ContextVarNode::from(index).latest_version(self);
                let parent = ContextVarNode::from(parent).latest_version(self);
                let idx = self.advance_var_in_ctx(index, loc, ctx)?;
                if !parent.is_mapping(self).into_expr_err(loc)? && parent.is_indexable(self).into_expr_err(loc)? {
                    let len_var = self.tmp_length(parent, ctx, loc).latest_version(self);
                    self.handle_require_inner(
                        ctx,
                        loc,
                        &ExprRet::Single(len_var.latest_version(self).into()),
                        &ExprRet::Single(idx.latest_version(self).into()),
                        RangeOp::Gt,
                        RangeOp::Lt,
                        (RangeOp::Lte, RangeOp::Gte),
                    )?;
                }

                let name = format!("{}[{}]", parent.name(self).into_expr_err(loc)?, index.name(self).into_expr_err(loc)?);

                if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
                    let index_var = index_var.latest_version(self);
                    let index_var = self.advance_var_in_ctx(index_var, loc, ctx)?;
                    ctx.push_expr(ExprRet::Single(index_var.into()), self).into_expr_err(loc)?;
                    Ok(())
                } else {
                    let ty = parent.ty(self).into_expr_err(loc)?.clone();
                    let ty = ty.get_index_dynamic_ty(index, self).into_expr_err(loc)?;
                    let index_var = ContextVar {
                        loc: Some(loc),
                        name: name.clone(),
                        display_name: format!(
                            "{}[{}]",
                            parent.display_name(self).into_expr_err(loc)?,
                            index.display_name(self).into_expr_err(loc)?
                        ),
                        storage: *parent.storage(self).into_expr_err(loc)?,
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        is_return: false,
                        ty,
                    };

                    let idx_node = self.add_node(Node::ContextVar(index_var));
                    self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                    self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(idx_node.into(), self).into_expr_err(loc)?;
                    self.add_edge(index, idx_node, Edge::Context(ContextEdge::Index));

                    ctx.push_expr(ExprRet::Single(idx_node), self).into_expr_err(loc)?;
                    Ok(())
                }
            }
            e => Err(ExprErr::ArrayIndex(loc, format!("Expected single expr evaluation of index expression, but was: {e:?}. This is a bug. Please report it at github.com/nascentxyz/pyrometer."))),
        }
    }
}
