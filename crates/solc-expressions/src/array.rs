use graph::elem::RangeElem;
use crate::{
    require::Require, variable::Variable, ContextBuilder, ExprErr, ExpressionParser, IntoExprErr,
    ListAccess,
};

use graph::{
    elem::{Elem, RangeOp, RangeDyn},
    range_string::ToRangeString,
    nodes::{TmpConstruction, Builtin, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, VarType, Range,
};

use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Loc},
};

impl<T> Array for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles arrays
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
                let _ = self.index_into_array_raw(ctx, loc, index, parent, true, false)?;
                Ok(())
            }
            e => Err(ExprErr::ArrayIndex(loc, format!("Expected single expr evaluation of index expression, but was: {e:?}. This is a bug. Please report it at github.com/nascentxyz/pyrometer."))),
        }
    }

    fn index_into_array_raw(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        index: ContextVarNode,
        parent: ContextVarNode,
        length_requirement: bool,
        return_var: bool,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        println!("access array: {}, parent: {}", index.display_name(self).unwrap(), parent.display_name(self).unwrap());
        let idx = self.advance_var_in_ctx(index, loc, ctx)?;
        if length_requirement && !parent.is_mapping(self).into_expr_err(loc)? && parent.is_indexable(self).into_expr_err(loc)? {
            let len_var = self.get_length(ctx, loc, parent, true)?.unwrap().latest_version(self);
            self.require(
                len_var.latest_version(self),
                idx.latest_version(self),
                ctx,
                loc,
                RangeOp::Gt,
                RangeOp::Lt,
                (RangeOp::Lte, RangeOp::Gte),
            )?;
        }

        let name = format!("{}[{}]", parent.name(self).into_expr_err(loc)?, index.name(self).into_expr_err(loc)?);
        if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            let index_var = index_var.latest_version(self);
            let index_var = self.advance_var_in_ctx(index_var, loc, ctx)?;
            if !return_var {
                ctx.push_expr(ExprRet::Single(index_var.into()), self).into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(index_var))
            }
        } else {
            let ty = parent.ty(self).into_expr_err(loc)?.clone();
            let ty = ty.get_index_dynamic_ty(index, self).into_expr_err(loc)?;
            // println!("index access ty: {:?#")
            let index_access_var = ContextVar {
                loc: Some(loc),
                name: name.clone(),
                display_name: format!(
                    "{}[{}]",
                    parent.display_name(self).into_expr_err(loc)?,
                    index.display_name(self).into_expr_err(loc)?
                ),
                storage: *parent.storage(self).into_expr_err(loc)?,
                is_tmp: false,
                tmp_of: Some(TmpConstruction::new(parent, RangeOp::SetIndices, Some(index))),
                is_symbolic: true,
                is_return: false,
                ty,
            };

            let idx_access_node = self.add_node(Node::ContextVar(index_access_var));
            self.add_edge(idx_access_node, parent, Edge::Context(ContextEdge::IndexAccess));
            self.add_edge(idx_access_node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.add_var(idx_access_node.into(), self).into_expr_err(loc)?;
            self.add_edge(index, idx_access_node, Edge::Context(ContextEdge::Index));

            let min = Elem::from(parent).get_index(index.into()).max(ContextVarNode::from(idx_access_node).into()); //.range_min(self).unwrap().unwrap());
            let max = Elem::from(parent).get_index(index.into()).min(ContextVarNode::from(idx_access_node).into()); //.range_max(self).unwrap().unwrap());
            
            let idx_access_cvar = self.advance_var_in_ctx_forcible(ContextVarNode::from(idx_access_node), loc, ctx, true)?;
            idx_access_cvar.set_range_min(self, min).into_expr_err(loc)?;
            idx_access_cvar.set_range_max(self, max).into_expr_err(loc)?;

            if idx_access_cvar
                .underlying(self)
                .into_expr_err(loc)?
                .ty
                .is_dyn_builtin(self)
                .into_expr_err(loc)?
            {
                // if the index access is also an array, produce a length variable
                // we specify to return the variable because we dont want it on the stack
                let _ = self.get_length(ctx, loc, idx_access_node.into(), true)?;

            }

            if !return_var {
                ctx.push_expr(ExprRet::Single(idx_access_cvar.latest_version(self).into()), self).into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(idx_access_cvar.latest_version(self)))
            }
        }
    }

    fn update_array_if_index_access(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        maybe_index_access: ContextVarNode,
        new_value: ContextVarNode
    ) -> Result<(), ExprErr> {
        // println!("checking if array access: {} (idx {})", maybe_index_access.display_name(self).unwrap(), maybe_index_access.0);
        if let Some(arr) = maybe_index_access.index_access_to_array(self) {
            // Was indeed an indexed value
            // println!("updating index to array: {}, index: {}", arr.display_name(self).unwrap(), maybe_index_access.display_name(self).unwrap());
            if let Some(index) = maybe_index_access.index_access_to_index(self) {
                // Found the associated index
                let next_arr = self.advance_var_in_ctx(arr.latest_version(self), loc, ctx)?;
                if next_arr
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .is_dyn_builtin(self)
                    .into_expr_err(loc)?
                {
                    // update the range
                    let min = Elem::from(arr).set_indices(RangeDyn::new_for_indices(vec![(index.into(), new_value.into())], loc));
                    let max = Elem::from(arr).set_indices(RangeDyn::new_for_indices(vec![(index.into(), new_value.into())], loc));
                    next_arr
                            .set_range_min(self, min)
                            .into_expr_err(loc)?;
                    next_arr
                            .set_range_max(self, max)
                            .into_expr_err(loc)?;
                }

                // handle nested arrays, i.e. if:
                // uint256[][] memory z;
                // z[x][y] = 5;
                // first pass sets z[x][y] = 5, second pass needs to set z[x] = x
                self.update_array_if_index_access(ctx, loc, next_arr.latest_version(self), next_arr.latest_version(self))?;
            }
        }
        Ok(())
    }

    fn update_array_if_length_var(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        maybe_length: ContextVarNode,
    ) -> Result<(), ExprErr> {
        if let Some(backing_arr) = maybe_length.len_var_to_array(self).into_expr_err(loc)? {
            let next_arr = self.advance_var_in_ctx(backing_arr.latest_version(self), loc, ctx)?;
            let new_len = Elem::from(backing_arr).set_length(maybe_length.into());
            next_arr
                    .set_range_min(self, new_len.clone())
                    .into_expr_err(loc)?;
            next_arr
                    .set_range_max(self, new_len)
                    .into_expr_err(loc)?;
        }
        Ok(())
    }

    fn set_var_as_length(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        new_length: ContextVarNode,
        backing_arr: ContextVarNode
    ) -> Result<(), ExprErr> {
        let next_arr = self.advance_var_in_ctx(backing_arr.latest_version(self), loc, ctx)?;
        let new_len = Elem::from(backing_arr).get_length().max(new_length.into());
        let min = Elem::from(backing_arr).set_length(new_len);
        next_arr
                .set_range_min(self, min)
                .into_expr_err(loc)?;
        let new_len = Elem::from(backing_arr).get_length().min(new_length.into());
        let max = Elem::from(backing_arr).set_length(new_len);
        next_arr
                .set_range_max(self, max)
                .into_expr_err(loc)?;
        self.add_edge(new_length, next_arr, Edge::Context(ContextEdge::AttrAccess("length")));
        Ok(())
    }

    fn update_array_from_index_access(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        index: ContextVarNode,
        access: ContextVarNode,
        backing_arr: ContextVarNode
    ) -> Result<(), ExprErr> {
        let next_arr = self.advance_var_in_ctx(backing_arr.latest_version(self), loc, ctx)?;
        if next_arr
            .underlying(self)
            .into_expr_err(loc)?
            .ty
            .is_dyn_builtin(self)
            .into_expr_err(loc)?
        {
            // update the range
            let min = Elem::from(backing_arr).set_indices(RangeDyn::new_for_indices(vec![(index.into(), access.into())], loc));
            let max = Elem::from(backing_arr).set_indices(RangeDyn::new_for_indices(vec![(index.into(), access.into())], loc));
            next_arr
                    .set_range_min(self, min)
                    .into_expr_err(loc)?;
            next_arr
                    .set_range_max(self, max)
                    .into_expr_err(loc)?;
        }

        // handle nested arrays
        if let (Some(backing_arr), Some(parent_nested_index)) = (next_arr.index_access_to_array(self), next_arr.index_access_to_index(self)) {
            self.update_array_from_index_access(ctx, loc, parent_nested_index, next_arr, backing_arr.latest_version(self))
        } else {
            Ok(())
        }
    }

    fn update_array_min_if_length(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        maybe_length: ContextVarNode,
    ) -> Result<(), ExprErr> {
        if let Some(backing_arr) = maybe_length.len_var_to_array(self).into_expr_err(loc)? {
            let next_arr = self.advance_var_in_ctx(backing_arr.latest_version(self), loc, ctx)?;
            let new_len = Elem::from(backing_arr).get_length().max(maybe_length.into());
            let min = Elem::from(backing_arr).set_length(new_len);
            next_arr
                    .set_range_min(self, min)
                    .into_expr_err(loc)?;
        }
        Ok(())
    }

    fn update_array_max_if_length(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        maybe_length: ContextVarNode,
    ) -> Result<(), ExprErr> {
        if let Some(backing_arr) = maybe_length.len_var_to_array(self).into_expr_err(loc)? {
            let next_arr = self.advance_var_in_ctx(backing_arr.latest_version(self), loc, ctx)?;
            let new_len = Elem::from(backing_arr).get_length().min(maybe_length.into());
            let max = Elem::from(backing_arr).set_length(new_len);
            next_arr
                    .set_range_max(self, max)
                    .into_expr_err(loc)?;
        }
        Ok(())
    }
}
