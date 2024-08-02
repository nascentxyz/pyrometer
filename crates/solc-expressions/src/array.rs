use crate::{require::Require, variable::Variable, ListAccess};

use graph::{
    elem::{Elem, RangeDyn, RangeOp},
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        TmpConstruction,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> Array for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles arrays
pub trait Array: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn slice_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        arr: ExprRet,
        start: Option<ExprRet>,
        end: Option<ExprRet>,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        let arr = ContextVarNode::from(arr.expect_single().into_expr_err(loc)?);
        let start = if let Some(start) = start {
            Elem::from(ContextVarNode::from(
                start.expect_single().into_expr_err(loc)?,
            ))
        } else {
            Elem::from(Concrete::from(0))
        };

        let end = if let Some(end) = end {
            Elem::from(ContextVarNode::from(
                end.expect_single().into_expr_err(loc)?,
            ))
        } else {
            Elem::from(arr).get_length()
        };

        let as_bn = self.builtin_or_add(Builtin::Uint(256)).index();
        let as_var =
            ContextVar::new_from_builtin(loc, BuiltInNode(as_bn), self).into_expr_err(loc)?;
        let slice_var = ContextVarNode::from(self.add_node(as_var));
        slice_var
            .set_range_min(self, arena, start)
            .into_expr_err(loc)?;
        slice_var
            .set_range_max(self, arena, end)
            .into_expr_err(loc)?;

        let new_range = Elem::from(arr).slice(Elem::from(slice_var));

        let mut new_arr = ContextVar {
            loc: Some(loc),
            name: format!("tmp_arr{}", ctx.new_tmp(self).into_expr_err(loc)?),
            display_name: "tmp_arr".to_string(),
            storage: None,
            is_tmp: true,
            is_symbolic: false,
            is_return: false,
            tmp_of: None,
            dep_on: None,
            ty: VarType::try_from_idx(self, arr.0.into()).unwrap(),
        };
        new_arr.set_range(From::from(new_range));

        let new_arr = ContextVarNode::from(self.add_node(new_arr));
        ctx.add_var(new_arr, self).into_expr_err(loc)?;
        self.add_edge(new_arr, ctx, Edge::Context(ContextEdge::Variable));

        let _ = self.create_length(arena, ctx, new_arr, true, loc)?;

        ctx.push_expr(ExprRet::Single(new_arr.0.into()), self)
            .into_expr_err(loc)
    }

    /// Gets the array type
    fn match_ty(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        ret: ExprRet,
        sized: Option<U256>,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(inner_ty) | ExprRet::SingleLiteral(inner_ty) => {
                // ie: uint[]
                // ie: uint[][]
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = if let Some(sized) = sized {
                        Builtin::SizedArray(sized, var_type)
                    } else {
                        Builtin::Array(var_type)
                    };

                    if let Some(idx) = self.builtins().get(&dyn_b) {
                        ctx.push_expr(ExprRet::Single(*idx), self)
                            .into_expr_err(loc)?;
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins_mut().insert(dyn_b, idx);
                        ctx.push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(loc)?;
                    }
                    Ok(())
                } else {
                    Err(ExprErr::ArrayTy(loc, "Expected to be able to convert to a var type from an index to determine array type. This is a bug. Please report it at github.com/nascentxyz/pyrometer.".to_string()))
                }
            }
            ExprRet::Multi(inner) => {
                // ie: unsure of syntax needed to get here. (not possible?)
                inner
                    .into_iter()
                    .map(|i| self.match_ty(ctx, loc, i, sized))
                    .collect::<Result<Vec<_>, ExprErr>>()?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Null => Ok(()),
        }
    }

    /// Indexes into an array
    #[tracing::instrument(level = "trace", skip_all)]
    fn index_into_array_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        inner_paths: ExprRet,
        index_paths: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match (inner_paths, index_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (_, ExprRet::CtxKilled(kind)) | (ExprRet::CtxKilled(kind), _) => {
                ctx.kill(self, loc, kind).into_expr_err(loc)
            }
            (ExprRet::Single(parent), ExprRet::Single(index)) | (ExprRet::Single(parent), ExprRet::SingleLiteral(index)) => {
                let index = ContextVarNode::from(index).latest_version_or_inherited_in_ctx(ctx, self);
                let parent = ContextVarNode::from(parent).latest_version_or_inherited_in_ctx(ctx, self);
                let _ = self.index_into_array_raw(arena, ctx, loc, index, parent, true, false)?;
                Ok(())
            }
            e => Err(ExprErr::ArrayIndex(loc, format!("Expected single expr evaluation of index expression, but was: {e:?}. This is a bug. Please report it at github.com/nascentxyz/pyrometer."))),
        }
    }

    fn index_into_array_raw(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        index: ContextVarNode,
        parent: ContextVarNode,
        length_requirement: bool,
        return_var: bool,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        let idx = self.advance_var_in_ctx(index, loc, ctx)?;
        if length_requirement
            && !parent.is_mapping(self).into_expr_err(loc)?
            && parent.is_indexable(self).into_expr_err(loc)?
        {
            let len_var = self
                .get_length(arena, ctx, parent, true, loc)?
                .unwrap()
                .latest_version_or_inherited_in_ctx(ctx, self);
            self.require(
                arena,
                ctx,
                len_var.latest_version_or_inherited_in_ctx(ctx, self),
                idx.latest_version_or_inherited_in_ctx(ctx, self),
                RangeOp::Gt,
                loc,
            )?;
        }
        let name = format!(
            "{}[{}]",
            parent.name(self).into_expr_err(loc)?,
            index.as_controllable_name(self, arena).into_expr_err(loc)?
        );
        if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            let index_var = index_var.latest_version_or_inherited_in_ctx(ctx, self);
            let index_var = self.advance_var_in_ctx(index_var, loc, ctx)?;
            if !return_var {
                ctx.push_expr(ExprRet::Single(index_var.into()), self)
                    .into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(index_var))
            }
        } else {
            let ty = parent.ty(self).into_expr_err(loc)?.clone();

            let ty = ty.dynamic_underlying_ty(self).into_expr_err(loc)?;
            let maybe_struct = ty.maybe_struct();

            let has_range = ty.ref_range(self).into_expr_err(loc)?.is_some();
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
                tmp_of: Some(TmpConstruction::new(
                    parent,
                    RangeOp::SetIndices,
                    Some(index),
                )),
                dep_on: {
                    let mut deps = parent.dependent_on(self, true).into_expr_err(loc)?;
                    deps.extend(index.dependent_on(self, true).into_expr_err(loc)?);
                    Some(deps)
                },
                is_symbolic: true,
                is_return: false,
                ty,
            };

            let idx_access_node = self.add_node(index_access_var);
            self.add_edge(
                idx_access_node,
                parent,
                Edge::Context(ContextEdge::IndexAccess),
            );

            if let Some(strukt) = maybe_struct {
                strukt
                    .add_fields_to_cvar(self, loc, ContextVarNode::from(idx_access_node))
                    .into_expr_err(loc)?;
            }

            self.add_edge(idx_access_node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.add_var(idx_access_node.into(), self)
                .into_expr_err(loc)?;
            self.add_edge(index, idx_access_node, Edge::Context(ContextEdge::Index));

            let idx_access_cvar = if has_range {
                let min = Elem::from(parent)
                    .get_index(index.into())
                    .max(ContextVarNode::from(idx_access_node).into()); //.range_min(self).unwrap().unwrap());
                let max = Elem::from(parent)
                    .get_index(index.into())
                    .min(ContextVarNode::from(idx_access_node).into()); //.range_max(self).unwrap().unwrap());
                let idx_access_cvar =
                    self.advance_var_in_ctx(ContextVarNode::from(idx_access_node), loc, ctx)?;

                idx_access_cvar
                    .set_range_min(self, arena, min)
                    .into_expr_err(loc)?;
                idx_access_cvar
                    .set_range_max(self, arena, max)
                    .into_expr_err(loc)?;

                if idx_access_cvar
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .is_dyn_builtin(self)
                    .into_expr_err(loc)?
                {
                    // if the index access is also an array, produce a length variable
                    // we specify to return the variable because we dont want it on the stack
                    let _ = self.get_length(arena, ctx, idx_access_cvar, true, loc)?;
                }
                idx_access_cvar
            } else {
                ContextVarNode::from(idx_access_node)
            };

            if !return_var {
                ctx.push_expr(
                    ExprRet::Single(
                        idx_access_cvar
                            .latest_version_or_inherited_in_ctx(ctx, self)
                            .into(),
                    ),
                    self,
                )
                .into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(
                    idx_access_cvar.latest_version_or_inherited_in_ctx(ctx, self),
                ))
            }
        }
    }

    fn update_array_if_index_access(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        maybe_index_access: ContextVarNode,
        new_value: ContextVarNode,
    ) -> Result<(), ExprErr> {
        if let Some(arr) = maybe_index_access.index_access_to_array(self) {
            // Was indeed an indexed value
            if let Some(index) = maybe_index_access.index_access_to_index(self) {
                // Found the associated index
                let next_arr = self.advance_var_in_ctx(
                    arr.latest_version_or_inherited_in_ctx(ctx, self),
                    loc,
                    ctx,
                )?;
                if next_arr
                    .underlying(self)
                    .into_expr_err(loc)?
                    .ty
                    .is_dyn_builtin(self)
                    .into_expr_err(loc)?
                {
                    // update the range
                    let min = Elem::from(arr).set_indices(RangeDyn::new_for_indices(
                        vec![(index.into(), new_value.into())],
                        loc,
                    ));
                    let max = Elem::from(arr).set_indices(RangeDyn::new_for_indices(
                        vec![(index.into(), new_value.into())],
                        loc,
                    ));

                    next_arr
                        .set_range_min(self, arena, min)
                        .into_expr_err(loc)?;
                    next_arr
                        .set_range_max(self, arena, max)
                        .into_expr_err(loc)?;
                }

                // handle nested arrays, i.e. if:
                // uint256[][] memory z;
                // z[x][y] = 5;
                // first pass sets z[x][y] = 5, second pass needs to set z[x] = x
                self.update_array_if_index_access(
                    arena,
                    ctx,
                    loc,
                    next_arr.latest_version_or_inherited_in_ctx(ctx, self),
                    next_arr.latest_version_or_inherited_in_ctx(ctx, self),
                )?;
            }
        }
        Ok(())
    }

    fn set_var_as_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        new_length: ContextVarNode,
        backing_arr: ContextVarNode,
    ) -> Result<(), ExprErr> {
        let next_arr = self.advance_var_in_ctx(
            backing_arr.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
            ctx,
        )?;
        let new_len = Elem::from(backing_arr).get_length().max(new_length.into());
        let min = Elem::from(backing_arr).set_length(new_len);

        let new_len = Elem::from(backing_arr).get_length().min(new_length.into());
        let max = Elem::from(backing_arr).set_length(new_len);

        next_arr
            .set_range_min(self, arena, min)
            .into_expr_err(loc)?;
        next_arr
            .set_range_max(self, arena, max)
            .into_expr_err(loc)?;

        self.add_edge(
            new_length,
            next_arr,
            Edge::Context(ContextEdge::AttrAccess("length")),
        );
        Ok(())
    }

    fn update_array_from_index_access(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        index: ContextVarNode,
        access: ContextVarNode,
        backing_arr: ContextVarNode,
    ) -> Result<(), ExprErr> {
        let next_arr = self.advance_var_in_ctx(
            backing_arr.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
            ctx,
        )?;
        if next_arr
            .underlying(self)
            .into_expr_err(loc)?
            .ty
            .is_dyn_builtin(self)
            .into_expr_err(loc)?
        {
            // update the range
            let min = Elem::from(backing_arr).set_indices(RangeDyn::new_for_indices(
                vec![(index.into(), access.into())],
                loc,
            ));
            let max = Elem::from(backing_arr).set_indices(RangeDyn::new_for_indices(
                vec![(index.into(), access.into())],
                loc,
            ));
            next_arr
                .set_range_min(self, arena, min)
                .into_expr_err(loc)?;
            next_arr
                .set_range_max(self, arena, max)
                .into_expr_err(loc)?;
        }

        // handle nested arrays
        if let (Some(backing_arr), Some(parent_nested_index)) = (
            next_arr.index_access_to_array(self),
            next_arr.index_access_to_index(self),
        ) {
            self.update_array_from_index_access(
                arena,
                ctx,
                loc,
                parent_nested_index,
                next_arr,
                backing_arr.latest_version_or_inherited_in_ctx(ctx, self),
            )
        } else {
            Ok(())
        }
    }
}
