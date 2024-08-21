use crate::variable::Variable;

use graph::{
    elem::{Elem, RangeDyn, RangeElem},
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};

use shared::{ExprErr, IntoExprErr, RangeArena, StorageLocation};
use solang_parser::pt::{Expression, Loc};

impl<T> Assign for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles assignments
pub trait Assign: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Match on the [`ExprRet`]s of an assignment expression
    fn match_assign_sides(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
    ) -> Result<(), ExprErr> {
        match (lhs_paths, rhs_paths) {
            (_, ExprRet::Null) | (ExprRet::Null, _) => Ok(()),
            (ExprRet::CtxKilled(kind), _) | (_, ExprRet::CtxKilled(kind)) => {
                ctx.kill(self, loc, *kind).into_expr_err(loc)?;
                Ok(())
            }

            (lhs @ ExprRet::Single(_), rhs @ ExprRet::SingleLiteral(_)) => {
                // ie: uint x = 5;
                let lhs_cvar = ContextVarNode::from(lhs.expect_single().unwrap())
                    .latest_version_in_ctx(ctx, self)
                    .into_expr_err(loc)?;
                let rhs_cvar = ContextVarNode::from(rhs.expect_single().unwrap())
                    .latest_version_in_ctx(ctx, self)
                    .into_expr_err(loc)?;

                if rhs
                    .implicitly_castable_to_expr(self, lhs)
                    .into_expr_err(loc)?
                {
                    let tmp = rhs_cvar.as_tmp(self, ctx, loc).into_expr_err(loc)?;
                    tmp.literal_cast_from(&lhs_cvar, self).into_expr_err(loc)?;
                    ctx.push_expr(self.assign(arena, loc, lhs_cvar, tmp, ctx)?, self)
                        .into_expr_err(loc)
                } else {
                    Err(ExprErr::ParseError(
                        loc,
                        format!(
                            "Invalid solidity - {} cannot be implicitly cast to type: {}",
                            rhs_cvar
                                .ty(self)
                                .unwrap()
                                .as_string(self)
                                .into_expr_err(loc)?,
                            lhs_cvar
                                .ty(self)
                                .unwrap()
                                .as_string(self)
                                .into_expr_err(loc)?
                        ),
                    ))
                }
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                // ie: uint x = y;
                let lhs_cvar =
                    ContextVarNode::from(*lhs).latest_version_or_inherited_in_ctx(ctx, self);
                let rhs_cvar =
                    ContextVarNode::from(*rhs).latest_version_or_inherited_in_ctx(ctx, self);
                ctx.push_expr(self.assign(arena, loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), ExprRet::Multi(rhs_sides)) => {
                // ie: uint x = (a, b), not possible?
                rhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.match_assign_sides(arena, ctx, loc, l, expr_ret))
            }
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                // ie: (uint x, uint y) = a, not possible?
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.match_assign_sides(arena, ctx, loc, expr_ret, r))
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                // (x, y) = (a, b)
                // ie: (x, y) = (a, b, c), not possible?
                if lhs_sides.len() == rhs_sides.len() {
                    // (x, y) = (a, b)
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_assign_sides(arena, ctx, loc, lhs_expr_ret, rhs_expr_ret)
                        },
                    )
                } else {
                    // ie: (x, y) = (a, b, c), not possible?
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.match_assign_sides(arena, ctx, loc, lhs_paths, rhs_expr_ret)
                    })
                }
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    /// Perform an assignment
    #[tracing::instrument(level = "trace", skip_all)]
    fn assign(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        self.assign_inner(arena, loc, lhs_cvar, rhs_cvar, ctx, false)
    }

    fn assign_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        location_recursion_avoidance: bool,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "assigning: {} to {}",
            rhs_cvar.display_name(self).unwrap(),
            lhs_cvar.display_name(self).unwrap(),
        );

        debug_assert!(lhs_cvar != rhs_cvar);

        // TODO: evaluate if this is needed
        rhs_cvar
            .cast_from(&lhs_cvar, self, arena)
            .into_expr_err(loc)?;

        // if its storage/memory = storage/memory, sometimes we have to update the alias
        if !location_recursion_avoidance {
            self.maybe_handle_location_alias(arena, ctx, lhs_cvar, rhs_cvar, loc)?;
        }
        // if its a struct/error, we have to handle the assignment to fields
        if let Some(ret) = self.maybe_handle_fielded(arena, ctx, lhs_cvar, rhs_cvar, loc)? {
            return Ok(ret);
        }

        let new_lhs = self.update_lhs(arena, ctx, lhs_cvar, rhs_cvar, loc)?;
        self.add_assignment_edges(new_lhs, rhs_cvar, loc)?;
        // if its an index access, we need to handle the update to the parent array's range
        self.maybe_assign_to_parent_array(arena, ctx, new_lhs, rhs_cvar, loc)?;
        // if its an array to array assignment, we need to handle the length
        self.maybe_assign_array_to_array(arena, ctx, new_lhs, rhs_cvar, loc)?;

        if let Some(rhs_range) = rhs_cvar.ref_range(self).into_expr_err(loc)? {
            let res = new_lhs
                .latest_version_or_inherited_in_ctx(ctx, self)
                .try_set_range_exclusions(self, rhs_range.exclusions.clone())
                .into_expr_err(loc);
            let _ = self.add_if_err(res);
        }

        Ok(ExprRet::Single(new_lhs.into()))
    }

    fn update_lhs(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        // Construct new range for lhs
        let new_range_elem = Elem::from(rhs_cvar.latest_version_or_inherited_in_ctx(ctx, self));
        // Check if the rhs depends on the lhs.
        let needs_forcible = new_range_elem
            .depends_on(lhs_cvar, &mut vec![], self, arena)
            .into_expr_err(loc)?;

        // make a new left hand side
        let new_lhs = self.advance_var_in_ctx_forcible(
            arena,
            lhs_cvar.latest_version_or_inherited_in_ctx(ctx, self),
            loc,
            ctx,
            needs_forcible,
        )?;
        new_lhs.underlying_mut(self).into_expr_err(loc)?.tmp_of =
            rhs_cvar.tmp_of(self).into_expr_err(loc)?;

        if let Some(ref mut dep_on) = new_lhs.underlying_mut(self).into_expr_err(loc)?.dep_on {
            dep_on.push(rhs_cvar);
            dep_on.sort();
            dep_on.dedup();
        } else {
            new_lhs.set_dependent_on(self).into_expr_err(loc)?;
        }

        // we use try_set_* because some types like functions dont have a range.
        new_lhs
            .try_set_range_from_elem(self, arena, new_range_elem)
            .into_expr_err(loc)?;
        Ok(new_lhs)
    }

    fn add_assignment_edges(
        &mut self,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        if lhs_cvar.is_storage(self).into_expr_err(loc)? {
            self.add_edge(lhs_cvar, rhs_cvar, Edge::Context(ContextEdge::StorageWrite));
        }
        self.add_edge(lhs_cvar, rhs_cvar, Edge::Context(ContextEdge::Assign));

        if rhs_cvar.underlying(self).into_expr_err(loc)?.is_return {
            if let Some(rhs_ctx) = rhs_cvar.maybe_ctx(self) {
                self.add_edge(
                    rhs_cvar,
                    lhs_cvar,
                    Edge::Context(ContextEdge::ReturnAssign(
                        rhs_ctx.underlying(self).unwrap().is_ext_fn_call(),
                    )),
                );
            } else {
                todo!("Applies may set `is_return`, but we dont track that right now")
            }
        }
        Ok(())
    }

    fn maybe_handle_fielded(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<Option<ExprRet>, ExprErr> {
        if lhs_cvar.is_fielded(self).into_expr_err(loc)?
            && rhs_cvar.is_fielded(self).into_expr_err(loc)?
        {
            let ret = self.assign_fielded_to_fielded(arena, ctx, lhs_cvar, rhs_cvar, loc)?;
            Ok(Some(ret))
        } else {
            Ok(None)
        }
    }

    fn maybe_handle_location_alias(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        maybe_alias: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        // if the rhs is index access, maintains that index access
        let mut newly_created_alias = false;

        let matching_loc = matches!(
            (
                maybe_alias.storage(self).into_expr_err(loc)?,
                rhs.storage(self).into_expr_err(loc)?
            ),
            (
                Some(StorageLocation::StoragePtr(_)),
                Some(StorageLocation::StoragePtr(_))
            ) | (
                Some(StorageLocation::StoragePtr(_)),
                Some(StorageLocation::Storage(_))
            ) | (
                Some(StorageLocation::MemoryPtr(_)),
                Some(StorageLocation::MemoryPtr(_))
            ) | (
                Some(StorageLocation::MemoryPtr(_)),
                Some(StorageLocation::Memory(_))
            )
        );

        if matching_loc && maybe_alias.maybe_location_alias(self).is_none() {
            tracing::trace!("lhs was storage/memory ptr");
            newly_created_alias = true;
            // rhs was an alias
            let mut curr_origin = rhs;
            while let Some(aliased_rhs) = curr_origin.maybe_location_alias(self) {
                curr_origin = aliased_rhs;
            }
            self.add_edge(
                maybe_alias,
                curr_origin.first_version(self),
                Edge::Context(ContextEdge::LocationAlias),
            );
        }

        if !newly_created_alias {
            if let Some(alias) = maybe_alias.maybe_location_alias(self) {
                tracing::trace!(
                    "lhs was a storage or memory pointer, assign the alias ({}) to the rhs",
                    alias.name(self).unwrap()
                );
                let incoming_aliases = alias.maybe_incoming_aliases(self);
                let _ = self.assign(
                    arena,
                    loc,
                    alias.latest_version(self),
                    rhs.latest_version(self),
                    ctx,
                )?;
                incoming_aliases
                    .into_iter()
                    .filter(|incoming_alias| *incoming_alias != maybe_alias)
                    .try_for_each(|incoming_alias| {
                        let _ = self.assign_inner(
                            arena,
                            loc,
                            incoming_alias.latest_version(self),
                            alias.latest_version(self),
                            ctx,
                            true,
                        )?;
                        Ok(())
                    })?;
            }
        }
        Ok(())
    }

    fn maybe_assign_to_parent_array(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        maybe_arr_attr: ContextVarNode,
        rhs: ContextVarNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "checking if {} is an index/length into/of an array",
            maybe_arr_attr.display_name(self).unwrap()
        );
        if let Some(index) = maybe_arr_attr.index_access_to_index(self) {
            let array = maybe_arr_attr.index_access_to_array(self).unwrap();
            tracing::trace!(
                "{} is an index into {}. rhs: {:#?}",
                ExprRet::from(maybe_arr_attr).debug_str_ranged(self, arena),
                array.display_name(self).unwrap(),
                rhs.range_max(self)
                    .unwrap()
                    .unwrap()
                    .recurse_dearenaize(arena),
            );
            let latest_arr = array.latest_version_or_inherited_in_ctx(ctx, self);
            let new_arr = self.advance_var_in_ctx_forcible(arena, latest_arr, loc, ctx, true)?;
            let new_elem = Elem::from(latest_arr).set_indices(RangeDyn::new_for_indices(
                vec![(Elem::from(index), Elem::from(rhs))],
                loc,
            ));
            new_arr
                .set_range_min(self, arena, new_elem.clone())
                .into_expr_err(loc)?;
            new_arr
                .set_range_max(self, arena, new_elem)
                .into_expr_err(loc)?;

            self.maybe_assign_to_parent_array(arena, ctx, latest_arr, new_arr, loc)?;
        }

        if let Some(array) = maybe_arr_attr.len_var_to_array(self) {
            tracing::trace!(
                "{} is an index into {}",
                maybe_arr_attr.display_name(self).unwrap(),
                array.display_name(self).unwrap(),
            );
            let latest_arr = array.latest_version_or_inherited_in_ctx(ctx, self);
            let new_arr = self.advance_var_in_ctx_forcible(arena, latest_arr, loc, ctx, true)?;
            let new_elem = Elem::from(latest_arr).set_length(Elem::from(rhs));
            new_arr
                .set_range_min(self, arena, new_elem.clone())
                .into_expr_err(loc)?;
            new_arr
                .set_range_max(self, arena, new_elem)
                .into_expr_err(loc)?;

            self.maybe_assign_to_parent_array(arena, ctx, latest_arr, new_arr, loc)?;
        }

        Ok(())
    }

    fn maybe_assign_array_to_array(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        if let Some(rhs_len_var) = rhs_cvar.array_to_len_var(self) {
            if let Some(lhs_len_var) = lhs_cvar.array_to_len_var(self) {
                self.assign(arena, loc, lhs_len_var, rhs_len_var, ctx)?;
            }
        }

        Ok(())
    }

    fn assign_fielded_to_fielded(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        let lhs_fields = lhs_cvar.fielded_to_fields(self).into_expr_err(loc)?;
        let rhs_fields = rhs_cvar.fielded_to_fields(self).into_expr_err(loc)?;
        lhs_fields.iter().try_for_each(|lhs_field| {
            let lhs_full_name = lhs_field.display_name(self).into_expr_err(loc)?;
            let split = lhs_full_name.split('.').collect::<Vec<_>>();
            let Some(lhs_field_name) = split.last() else {
                return Err(ExprErr::ParseError(
                    lhs_field.loc(self).unwrap(),
                    format!("Incorrectly named field: {lhs_full_name} - no '.' delimiter"),
                ));
            };

            let mut found = false;
            for rhs_field in rhs_fields.iter() {
                let rhs_full_name = rhs_field.display_name(self).into_expr_err(loc)?;
                let split = rhs_full_name.split('.').collect::<Vec<_>>();
                let Some(rhs_field_name) = split.last() else {
                    return Err(ExprErr::ParseError(
                        rhs_field.loc(self).unwrap(),
                        format!("Incorrectly named field: {rhs_full_name} - no '.' delimiter"),
                    ));
                };
                if lhs_field_name == rhs_field_name {
                    found = true;
                    let _ = self.assign(arena, loc, *lhs_field, *rhs_field, ctx)?;
                    break;
                }
            }
            if found {
                Ok(())
            } else {
                Err(ExprErr::ParseError(
                    loc,
                    format!("Struct types mismatched - could not find field: {lhs_field_name}"),
                ))
            }
        })?;

        self.maybe_assign_to_parent_array(arena, ctx, lhs_cvar, rhs_cvar, loc)?;
        self.maybe_assign_array_to_array(arena, ctx, lhs_cvar, rhs_cvar, loc)?;
        Ok(ExprRet::Single(lhs_cvar.latest_version(self).0.into()))
    }
}
