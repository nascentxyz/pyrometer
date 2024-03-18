use crate::{
    array::Array, variable::Variable, ContextBuilder, ExprErr, ExpressionParser, IntoExprErr,
    ListAccess,
};

use graph::{
    elem::{RangeElem, Elem},
    nodes::{ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, GraphError, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> Assign for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles assignments
pub trait Assign: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Parse an assignment expression
    fn assign_exprs(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(rhs_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(rhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "Assign operation had no right hand side".to_string(),
                ));
            };

            if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.parse_ctx_expr(lhs_expr, ctx)?;
            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(lhs_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(
                        loc,
                        "Assign operation had no left hand side".to_string(),
                    ));
                };
                if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                analyzer.match_assign_sides(ctx, loc, &lhs_paths.flatten(), &rhs_paths)?;
                Ok(())
            })
        })
    }

    /// Match on the [`ExprRet`]s of an assignment expression
    fn match_assign_sides(
        &mut self,
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
            (ExprRet::Single(lhs), ExprRet::SingleLiteral(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                let res = rhs_cvar
                    .literal_cast_from(&lhs_cvar, self)
                    .into_expr_err(loc);
                let _ = self.add_if_err(res);
                ctx.push_expr(self.assign(loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (ExprRet::Single(lhs), ExprRet::Single(rhs)) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                ctx.push_expr(self.assign(loc, lhs_cvar, rhs_cvar, ctx)?, self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            (l @ ExprRet::Single(_), ExprRet::Multi(rhs_sides)) => rhs_sides
                .iter()
                .try_for_each(|expr_ret| self.match_assign_sides(ctx, loc, l, expr_ret)),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_) | r @ ExprRet::SingleLiteral(_)) => {
                lhs_sides
                    .iter()
                    .try_for_each(|expr_ret| self.match_assign_sides(ctx, loc, expr_ret, r))
            }
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).try_for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_assign_sides(ctx, loc, lhs_expr_ret, rhs_expr_ret)
                        },
                    )
                } else {
                    rhs_sides.iter().try_for_each(|rhs_expr_ret| {
                        self.match_assign_sides(ctx, loc, lhs_paths, rhs_expr_ret)
                    })
                }
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    /// Perform an assignment
    fn assign(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "assigning: {} to {}",
            rhs_cvar.display_name(self).unwrap(),
            lhs_cvar.display_name(self).unwrap(),
        );

        let (new_lower_bound, new_upper_bound) = (
            Elem::from(rhs_cvar.latest_version(self)),
            Elem::from(rhs_cvar.latest_version(self)),
        );



        let needs_forcible = new_lower_bound.depends_on(lhs_cvar, &mut vec![], self).into_expr_err(loc)?
        || new_upper_bound.depends_on(lhs_cvar, &mut vec![], self).into_expr_err(loc)?;

        let new_lhs = if needs_forcible {
            self.advance_var_in_ctx_forcible(lhs_cvar.latest_version(self), loc, ctx, true)?
        } else {
            self.advance_var_in_ctx(lhs_cvar.latest_version(self), loc, ctx)?    
        };
        
        new_lhs.underlying_mut(self).into_expr_err(loc)?.tmp_of =
            rhs_cvar.tmp_of(self).into_expr_err(loc)?;
        if lhs_cvar.is_storage(self).into_expr_err(loc)? {
            self.add_edge(new_lhs, rhs_cvar, Edge::Context(ContextEdge::StorageWrite));
        }

        if rhs_cvar.underlying(self).into_expr_err(loc)?.is_return {
            if let Some(rhs_ctx) = rhs_cvar.maybe_ctx(self) {
                self.add_edge(
                    rhs_cvar,
                    new_lhs,
                    Edge::Context(ContextEdge::ReturnAssign(
                        rhs_ctx.underlying(self).unwrap().ext_fn_call.is_some(),
                    )),
                );
            } else {
                return Err(ExprErr::GraphError(
                    loc,
                    GraphError::DetachedVariable(format!(
                        "No context for variable: {}, node idx: {}, curr ctx: {}, lhs ctx: {}",
                        rhs_cvar.display_name(self).unwrap(),
                        rhs_cvar.0,
                        ctx.path(self),
                        lhs_cvar.ctx(self).path(self)
                    )),
                ));
            }
        }

        if !lhs_cvar.ty_eq(&rhs_cvar, self).into_expr_err(loc)? {
            let cast_to_min = match lhs_cvar.range_min(self).into_expr_err(loc)? {
                Some(v) => v,
                None => {
                    return Err(ExprErr::BadRange(
                        loc,
                        format!(
                            "No range during cast? {:?}, {:?}",
                            lhs_cvar.underlying(self).unwrap(),
                            rhs_cvar.underlying(self).unwrap(),
                        ),
                    ))
                }
            };

            let cast_to_max = match lhs_cvar.range_max(self).into_expr_err(loc)? {
                Some(v) => v,
                None => {
                    return Err(ExprErr::BadRange(
                        loc,
                        format!(
                            "No range during cast? {:?}, {:?}",
                            lhs_cvar.underlying(self).unwrap(),
                            rhs_cvar.underlying(self).unwrap(),
                        ),
                    ))
                }
            };

            let _ = new_lhs.try_set_range_min(self, new_lower_bound.cast(cast_to_min));
            let _ = new_lhs.try_set_range_max(self, new_upper_bound.cast(cast_to_max));
        } else {
            let _ = new_lhs.try_set_range_min(self, new_lower_bound);
            let _ = new_lhs.try_set_range_max(self, new_upper_bound);
        }
        if let Some(rhs_range) = rhs_cvar.ref_range(self).into_expr_err(loc)? {
            let res = new_lhs
                .try_set_range_exclusions(self, rhs_range.exclusions.clone())
                .into_expr_err(loc);
            let _ = self.add_if_err(res);
        }

        if rhs_cvar.is_indexable(self).into_expr_err(loc)? {
            // rhs is indexable. get the length attribute, create a new length for the lhs,
            // and perform assign
            let rhs_len_cvar = self.get_length(ctx, loc, rhs_cvar, true)?.unwrap();
            let lhs_len_cvar = self.get_length(ctx, loc, lhs_cvar, true)?.unwrap();
            self.assign(loc, lhs_len_cvar, rhs_len_cvar, ctx)?;
            // update the range
            self.update_array_if_length_var(ctx, loc, lhs_len_cvar.latest_version(self))?;
        }

        self.update_array_if_index_access(ctx, loc, lhs_cvar, rhs_cvar)?;

        // handle struct assignment
        if let Ok(fields) = rhs_cvar.struct_to_fields(self) {
            if !fields.is_empty() {
                fields.into_iter().for_each(|field| {
                    let mut new_var = field.underlying(self).unwrap().clone();
                    let field_name = field.name(self).unwrap();
                    let field_name = field_name.split('.').collect::<Vec<_>>()[1];
                    let new_name = format!("{}.{field_name}", lhs_cvar.name(self).unwrap());
                    new_var.name = new_name.clone();
                    new_var.display_name = new_name;
                    let new_field =
                        ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));
                    self.add_edge(new_field, lhs_cvar.first_version(self), Edge::Context(ContextEdge::AttrAccess("field")));
                })
            }
        }

        // advance the rhs variable to avoid recursion issues
        self.advance_var_in_ctx_forcible(rhs_cvar.latest_version(self), loc, ctx, true)?;
        Ok(ExprRet::Single(new_lhs.into()))
    }
}
