use crate::{require::Require, variable::Variable, Assign, ErrType, ListAccess};

use graph::{
    elem::{Elem, RangeDyn, RangeOp},
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet,
        TmpConstruction,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use alloy_primitives::U256;
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

        if let (Some(s), Some(e)) = (&start, &end) {
            self.handle_require_inner(arena, ctx, e, s, RangeOp::Gte, Some(ErrType::Revert), loc)?;
        }

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
            is_fundamental: None,
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
        let idx = self.advance_var_in_ctx(arena, index, loc, ctx)?;
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
                ErrType::index_oob(),
                loc,
            )?;

            let latest = len_var.latest_version_or_inherited_in_ctx(ctx, self);
            // need to update parent's length
            self.maybe_assign_to_parent_array(arena, ctx, len_var, latest, loc)?;
        }

        let idx_name = if index.is_const(self, arena).into_expr_err(loc)? {
            let min = index.evaled_range_min(self, arena).unwrap().unwrap();
            match min {
                Elem::Concrete(c) => {
                    format!("{}", c.val)
                }
                Elem::ConcreteDyn(rd) => {
                    if let Some(raw_bytes) = rd.as_bytes(self, false, arena) {
                        if index
                            .ty(self)
                            .into_expr_err(loc)?
                            .is_string(self)
                            .into_expr_err(loc)?
                        {
                            String::from_utf8_lossy(&raw_bytes[..]).to_string()
                        } else {
                            format!("0x{}", hex::encode(raw_bytes))
                        }
                    } else {
                        index.as_controllable_name(self, arena).into_expr_err(loc)?
                    }
                }
                _ => index.as_controllable_name(self, arena).into_expr_err(loc)?,
            }
        } else {
            index.as_controllable_name(self, arena).into_expr_err(loc)?
        };
        let name = format!("{}[{idx_name}]", parent.name(self).into_expr_err(loc)?,);
        if let Some(index_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            let index_var = index_var.latest_version_or_inherited_in_ctx(ctx, self);
            let index_var = self.advance_var_in_ctx_forcible(arena, index_var, loc, ctx, true)?;
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
                is_fundamental: None,
                ty,
            };

            let idx_access_node = self.add_node(index_access_var);
            self.add_edge(
                idx_access_node,
                parent,
                Edge::Context(ContextEdge::IndexAccess),
            );

            ContextVarNode::from(idx_access_node)
                .maybe_add_fields(self)
                .into_expr_err(loc)?;
            ContextVarNode::from(idx_access_node)
                .maybe_add_len_inplace(self, arena, ctx, loc)
                .into_expr_err(loc)?;

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
                let idx_access_cvar = self.advance_var_in_ctx(
                    arena,
                    ContextVarNode::from(idx_access_node),
                    loc,
                    ctx,
                )?;

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

            if let Some(aliased) = parent.maybe_location_alias(self) {
                // create the idx in the dealiased array
                if let Some(non_aliased) = self.index_into_array_raw(
                    arena,
                    ctx,
                    loc,
                    index.latest_version(self),
                    aliased,
                    length_requirement,
                    true,
                )? {
                    // rhs was an alias
                    let mut curr_origin = non_aliased;
                    while let Some(aliased_rhs) = curr_origin.maybe_location_alias(self) {
                        curr_origin = aliased_rhs;
                    }

                    self.add_edge(
                        idx_access_cvar.first_version(self),
                        curr_origin.first_version(self),
                        Edge::Context(ContextEdge::LocationAlias),
                    );

                    let incoming_aliases = aliased.maybe_incoming_aliases(self);
                    incoming_aliases
                        .into_iter()
                        .filter(|incoming_alias| *incoming_alias != parent)
                        .try_for_each(|incoming_alias| {
                            // create the idx in all aliased arrays
                            if let Some(aliased) = self.index_into_array_raw(
                                arena,
                                ctx,
                                loc,
                                index.latest_version(self),
                                incoming_alias,
                                length_requirement,
                                true,
                            )? {
                                self.add_edge(
                                    aliased.first_version(self),
                                    curr_origin.first_version(self),
                                    Edge::Context(ContextEdge::LocationAlias),
                                );
                            }
                            Ok(())
                        })?;
                }
            }

            self.update_array_from_index_access(arena, ctx, loc, index, idx_access_cvar, parent)?;

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

    fn set_var_as_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        new_length: ContextVarNode,
        backing_arr: ContextVarNode,
    ) -> Result<(), ExprErr> {
        let next_arr = self.advance_var_in_ctx(
            arena,
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
            arena,
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
