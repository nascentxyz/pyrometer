use crate::context_builder::StatementParser;
use crate::helper::CallerHelper;
use crate::member_access::ListAccess;
use crate::variable::Variable;

use graph::{
    elem::{Elem, RangeElem, RangeExpr, RangeOp},
    nodes::{
        Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode,
        FunctionParamNode, KilledKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, Range, SolcRange, VarType,
};
use shared::{AnalyzerLike, ExprErr, IntoExprErr, NodeIdx, RangeArena, StorageLocation};

use solang_parser::pt::{Expression, Loc};

use std::collections::BTreeMap;

impl<T> FuncJoiner for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>
        + Sized
        + GraphBackend
        + CallerHelper
        + JoinStatTracker
{
}
/// A trait for calling a function
pub trait FuncJoiner:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + JoinStatTracker
{
    #[tracing::instrument(level = "trace", skip_all)]
    fn join(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        func: FunctionNode,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
        seen: &mut Vec<FunctionNode>,
    ) -> Result<bool, ExprErr> {
        tracing::trace!(
            "Trying to join function: {}",
            func.name(self).into_expr_err(loc)?
        );
        // ensure no modifiers (for now)
        // if pure function:
        //      grab requirements for context
        //      grab return node's simplified range
        //      replace fundamentals with function inputs
        //      update ctx name in place

        if func.is_pure(self).into_expr_err(loc)? {
            // pure functions are guaranteed to not require the use of state, so
            // the only things we care about are function inputs and function outputs
            if let Some(body_ctx) = func.maybe_body_ctx(self) {
                if body_ctx
                    .underlying(self)
                    .into_expr_err(loc)?
                    .child
                    .is_some()
                {
                    tracing::trace!("Joining function: {}", func.name(self).into_expr_err(loc)?);
                    let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
                    match edges.len() {
                        0 => {}
                        1 => {
                            self.join_pure(
                                arena,
                                loc,
                                func,
                                params,
                                func_inputs,
                                body_ctx,
                                edges[0],
                                ctx,
                                false,
                            )?;
                            return Ok(true);
                        }
                        2.. => {
                            tracing::trace!(
                                "Branching pure join function: {}",
                                func.name(self).into_expr_err(loc)?
                            );
                            // self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                            let new_forks = ctx.set_join_forks(loc, edges.clone(), self).unwrap();
                            edges.into_iter().zip(new_forks.iter()).try_for_each(
                                |(edge, new_fork)| {
                                    let res = self.join_pure(
                                        arena,
                                        loc,
                                        func,
                                        params,
                                        func_inputs,
                                        body_ctx,
                                        edge,
                                        *new_fork,
                                        true,
                                    )?;
                                    if !res {
                                        new_fork
                                            .kill(self, loc, KilledKind::Unreachable)
                                            .into_expr_err(loc)?;
                                        Ok(())
                                    } else {
                                        Ok(())
                                    }
                                },
                            )?;
                            return Ok(true);
                        }
                    }
                } else {
                    tracing::trace!(
                        "Childless pure join: {}",
                        func.name(self).into_expr_err(loc)?
                    );
                    self.join_pure(
                        arena,
                        loc,
                        func,
                        params,
                        func_inputs,
                        body_ctx,
                        body_ctx,
                        ctx,
                        false,
                    )?;
                    return Ok(true);
                }
            } else {
                tracing::trace!("Pure function not processed");
                if ctx.associated_fn(self) == Ok(func) {
                    return Ok(false);
                }

                if seen.contains(&func) {
                    return Ok(false);
                }

                self.handled_funcs_mut().push(func);
                if let Some(body) = &func.underlying(self).unwrap().body.clone() {
                    self.parse_ctx_statement(arena, body, false, Some(func));
                }

                seen.push(func);
                return self.join(arena, ctx, loc, func, params, func_inputs, seen);
            }
        } else if func.is_view(self).into_expr_err(loc)? {
            if let Some(body_ctx) = func.maybe_body_ctx(self) {
                if body_ctx
                    .underlying(self)
                    .into_expr_err(loc)?
                    .child
                    .is_some()
                {
                    let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
                    if edges.len() == 1 {
                        tracing::trace!(
                            "View join function: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        self.add_completed_view(false, false, false, body_ctx);
                    } else {
                        tracing::trace!(
                            "Branching view join function: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        self.add_completed_view(false, false, true, body_ctx);
                    }
                } else {
                    tracing::trace!(
                        "Childless view join function: {}",
                        func.name(self).into_expr_err(loc)?
                    );
                    self.add_completed_view(false, true, false, body_ctx);
                }
            } else {
                tracing::trace!("View function not processed");
            }
        } else if let Some(body_ctx) = func.maybe_body_ctx(self) {
            if body_ctx
                .underlying(self)
                .into_expr_err(loc)?
                .child
                .is_some()
            {
                let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
                if edges.len() == 1 {
                    tracing::trace!("Mut join function: {}", func.name(self).into_expr_err(loc)?);
                    self.add_completed_mut(false, false, false, body_ctx);
                } else {
                    tracing::trace!(
                        "Branching mut join function: {}",
                        func.name(self).into_expr_err(loc)?
                    );
                    self.add_completed_mut(false, false, true, body_ctx);
                }
            } else {
                tracing::trace!(
                    "Childless mut join function: {}",
                    func.name(self).into_expr_err(loc)?
                );
                self.add_completed_mut(false, true, false, body_ctx);
            }
        } else {
            tracing::trace!("Mut function not processed");
        }

        Ok(false)
    }

    fn join_pure(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        func: FunctionNode,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
        body_ctx: ContextNode,
        resulting_edge: ContextNode,
        target_ctx: ContextNode,
        forks: bool,
    ) -> Result<bool, ExprErr> {
        let replacement_map =
            self.basic_inputs_replacement_map(arena, body_ctx, loc, params, func_inputs)?;
        let mut rets: Vec<_> = resulting_edge
            .return_nodes(self)
            .into_expr_err(loc)?
            .iter()
            .enumerate()
            .map(|(i, (_, ret_node))| {
                let mut new_var = ret_node.underlying(self).unwrap().clone();
                let new_name = format!("{}.{i}", func.name(self).unwrap());
                new_var.name.clone_from(&new_name);
                new_var.display_name = new_name;
                if let Some(mut range) = new_var.ty.take_range() {
                    let mut range: SolcRange =
                        range.take_flattened_range(self, arena).unwrap().into();
                    replacement_map.iter().for_each(|(replace, replacement)| {
                        range.replace_dep(*replace, replacement.0.clone(), self, arena);
                    });

                    range.cache_eval(self, arena).unwrap();
                    // TODO: change ty here to match ret type
                    new_var.ty.set_range(range).unwrap();
                }

                if let Some(ref mut dep_on) = &mut new_var.dep_on {
                    dep_on.iter_mut().for_each(|d| {
                        if let Some((_, r)) = replacement_map.get(&(*d).into()) {
                            *d = *r
                        }
                    });
                }

                let mut new_cvar = ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));
                self.add_edge(new_cvar, target_ctx, Edge::Context(ContextEdge::Variable));
                target_ctx.add_var(new_cvar, self).unwrap();

                // handle the case where the return node is a struct
                if let Ok(fields) = ret_node.struct_to_fields(self) {
                    if !fields.is_empty() {
                        fields.iter().for_each(|field| {
                            let mut new_var = field.underlying(self).unwrap().clone();
                            let new_name = format!(
                                "{}.{i}.{}",
                                func.name(self).unwrap(),
                                field.name(self).unwrap()
                            );
                            new_var.name.clone_from(&new_name);
                            new_var.display_name = new_name;
                            if let Some(mut range) = new_var.ty.take_range() {
                                let mut range: SolcRange =
                                    range.take_flattened_range(self, arena).unwrap().into();
                                replacement_map.iter().for_each(|(replace, replacement)| {
                                    range.replace_dep(*replace, replacement.0.clone(), self, arena);
                                });

                                range.cache_eval(self, arena).unwrap();

                                new_var.ty.set_range(range).unwrap();
                            }

                            if let Some(ref mut dep_on) = &mut new_var.dep_on {
                                dep_on.iter_mut().for_each(|d| {
                                    if let Some((_, r)) = replacement_map.get(&(*d).into()) {
                                        *d = *r
                                    }
                                });
                            }
                            let new_field =
                                ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));
                            self.add_edge(
                                new_field,
                                new_cvar,
                                Edge::Context(ContextEdge::AttrAccess("field")),
                            );
                        });
                    }
                } else {
                    let next_cvar = self
                        .advance_var_in_ctx_forcible(new_cvar, loc, target_ctx, true)
                        .unwrap();
                    let casted = Elem::Expr(RangeExpr::new(
                        Elem::from(new_cvar),
                        RangeOp::Cast,
                        Elem::from(*ret_node),
                    ));
                    next_cvar
                        .set_range_min(self, arena, casted.clone())
                        .unwrap();
                    next_cvar.set_range_max(self, arena, casted).unwrap();

                    new_cvar = next_cvar;
                }

                ExprRet::Single(new_cvar.latest_version(self).into())
            })
            .collect();

        let mut unsat = false;

        resulting_edge
            .ctx_deps(self)
            .into_expr_err(loc)?
            .iter()
            .try_for_each(|dep| {
                let mut new_var = dep.underlying(self)?.clone();
                if let Some(mut range) = new_var.ty.take_range() {
                    // let mut range: SolcRange =
                    // range.take_flattened_range(self).unwrap().into();
                    let mut range: SolcRange =
                        range.flattened_range(self, arena)?.into_owned().into();
                    replacement_map.iter().for_each(|(replace, replacement)| {
                        range.replace_dep(*replace, replacement.0.clone(), self, arena);
                    });

                    range.cache_eval(self, arena)?;
                    new_var.ty.set_range(range)?;
                }

                if let Some(ref mut dep_on) = &mut new_var.dep_on {
                    dep_on.iter_mut().for_each(|d| {
                        if let Some((_, r)) = replacement_map.get(&(*d).into()) {
                            *d = *r
                        }
                    });
                }
                let new_cvar = ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));

                if new_cvar.is_const(self, arena)?
                    && new_cvar.evaled_range_min(self, arena)?
                        == Some(Elem::from(Concrete::from(false)))
                {
                    unsat = true;
                }
                self.add_edge(new_cvar, target_ctx, Edge::Context(ContextEdge::Variable));
                target_ctx.add_var(new_cvar, self)?;
                target_ctx.add_ctx_dep(new_cvar, self, arena)
            })
            .into_expr_err(loc)?;

        if unsat {
            return Ok(false);
        }

        #[allow(clippy::unnecessary_to_owned)]
        func.returns(arena, self).into_iter().for_each(|ret| {
            if let Some(var) =
                ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).unwrap().clone())
            {
                let cvar = self.add_node(Node::ContextVar(var));
                target_ctx.add_var(cvar.into(), self).unwrap();
                self.add_edge(cvar, target_ctx, Edge::Context(ContextEdge::Variable));
                rets.push(ExprRet::Single(cvar));
            }
        });

        target_ctx.underlying_mut(self).into_expr_err(loc)?.path = format!(
            "{}.{}.resume{{ {} }}",
            target_ctx.path(self),
            resulting_edge.path(self),
            target_ctx.associated_fn_name(self).unwrap()
        );
        target_ctx
            .push_expr(ExprRet::Multi(rets), self)
            .into_expr_err(loc)?;
        self.add_completed_pure(true, false, forks, resulting_edge);
        Ok(true)
    }

    fn basic_inputs_replacement_map(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
    ) -> Result<BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>, ExprErr> {
        let inputs = ctx.input_variables(self);
        let mut replacement_map: BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)> =
            BTreeMap::default();
        params
            .iter()
            .zip(func_inputs.iter())
            .try_for_each(|(param, func_input)| {
                if let Some(name) = param.maybe_name(self).into_expr_err(loc)? {
                    let mut new_cvar = func_input
                        .latest_version(self)
                        .underlying(self)
                        .into_expr_err(loc)?
                        .clone();
                    new_cvar.loc = Some(param.loc(self).unwrap());
                    // new_cvar.name = name.clone();
                    // new_cvar.display_name = name.clone();
                    new_cvar.is_tmp = false;
                    new_cvar.storage = if let Some(StorageLocation::Storage(_)) =
                        param.underlying(self).unwrap().storage
                    {
                        new_cvar.storage
                    } else {
                        None
                    };

                    let replacement =
                        ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                    self.add_edge(
                        replacement,
                        *func_input,
                        Edge::Context(ContextEdge::InputVariable),
                    );

                    if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self).unwrap()) {
                        if !replacement.ty_eq_ty(&param_ty, self).into_expr_err(loc)? {
                            replacement
                                .cast_from_ty(param_ty, self, arena)
                                .into_expr_err(loc)?;
                        }
                    }

                    if let Some(_len_var) = replacement.array_to_len_var(self) {
                        // bring the length variable along as well
                        self.get_length(arena, ctx, loc, *func_input, false)
                            .unwrap();
                    }

                    if let (Some(r), Some(r2)) =
                        (replacement.range(self).unwrap(), param.range(self).unwrap())
                    {
                        let new_min = r.range_min().into_owned().cast(r2.range_min().into_owned());
                        let new_max = r.range_max().into_owned().cast(r2.range_max().into_owned());
                        replacement
                            .latest_version(self)
                            .try_set_range_min(self, arena, new_min)
                            .into_expr_err(loc)?;
                        replacement
                            .latest_version(self)
                            .try_set_range_max(self, arena, new_max)
                            .into_expr_err(loc)?;
                        replacement
                            .latest_version(self)
                            .try_set_range_exclusions(self, r.exclusions)
                            .into_expr_err(loc)?;
                    }

                    ctx.add_var(replacement, self).unwrap();
                    self.add_edge(replacement, ctx, Edge::Context(ContextEdge::Variable));

                    let Some(correct_input) = inputs
                        .iter()
                        .find(|input| input.name(self).unwrap() == name)
                    else {
                        return Err(ExprErr::InvalidFunctionInput(
                            loc,
                            "Could not match input to parameter".to_string(),
                        ));
                    };

                    if let Ok(fields) = correct_input.struct_to_fields(self) {
                        if !fields.is_empty() {
                            let replacement_fields = func_input.struct_to_fields(self).unwrap();
                            fields.iter().for_each(|field| {
                                let field_name = field.name(self).unwrap();
                                let to_replace_field_name =
                                    field_name.split('.').collect::<Vec<_>>()[1];
                                if let Some(replacement_field) =
                                    replacement_fields.iter().find(|replacement_field| {
                                        let name = replacement_field.name(self).unwrap();
                                        let replacement_name =
                                            name.split('.').collect::<Vec<_>>()[1];
                                        to_replace_field_name == replacement_name
                                    })
                                {
                                    let mut replacement_field_as_elem =
                                        Elem::from(*replacement_field);
                                    replacement_field_as_elem.arenaize(self, arena).unwrap();
                                    if let Some(next) = field.next_version(self) {
                                        replacement_map.insert(
                                            next.0.into(),
                                            (replacement_field_as_elem.clone(), *replacement_field),
                                        );
                                    }
                                    replacement_map.insert(
                                        field.0.into(),
                                        (replacement_field_as_elem, *replacement_field),
                                    );
                                }
                            });
                        }
                    }

                    let mut replacement_as_elem = Elem::from(replacement);
                    replacement_as_elem
                        .arenaize(self, arena)
                        .into_expr_err(loc)?;

                    if let Some(next) = correct_input.next_version(self) {
                        replacement_map
                            .insert(next.0.into(), (replacement_as_elem.clone(), replacement));
                    }
                    replacement_map
                        .insert(correct_input.0.into(), (replacement_as_elem, replacement));
                }
                Ok(())
            })?;
        Ok(replacement_map)
    }
}

impl<T> JoinStatTracker for T where T: AnalyzerLike + GraphBackend {}

pub trait JoinStatTracker: AnalyzerLike {
    fn add_completed_pure(
        &mut self,
        completed: bool,
        no_children: bool,
        forks: bool,
        target_ctx: ContextNode,
    ) where
        Self: Sized + GraphBackend,
    {
        match (no_children, forks) {
            (true, _) => {
                let num_vars = target_ctx.vars(self).len();
                let stats = self.join_stats_mut();
                stats.pure_no_children_joins.num_joins += 1;
                if completed {
                    stats.pure_no_children_joins.completed_joins += 1;
                }
                stats.pure_no_children_joins.vars_reduced += num_vars;
            }
            (false, false) => {
                let mut parents = target_ctx.parent_list(self).unwrap();
                parents.reverse();
                parents.push(target_ctx);
                let vars_reduced = parents.iter().fold(0, |mut acc, ctx| {
                    acc += ctx.vars(self).len();
                    acc
                });
                let stats = self.join_stats_mut();
                stats.pure_children_no_forks_joins.num_joins += 1;
                if completed {
                    stats.pure_children_no_forks_joins.completed_joins += 1;
                }
                stats.pure_children_no_forks_joins.vars_reduced += vars_reduced;
            }
            (false, true) => {
                let stats = self.join_stats_mut();
                stats.pure_children_forks_joins.num_joins += 1;
                if completed {
                    stats.pure_children_forks_joins.completed_joins += 1;
                }
            }
        }
    }

    fn add_completed_view(
        &mut self,
        completed: bool,
        no_children: bool,
        forks: bool,
        target_ctx: ContextNode,
    ) where
        Self: Sized + GraphBackend,
    {
        match (no_children, forks) {
            (true, _) => {
                let num_vars = target_ctx.vars(self).len();
                let stats = self.join_stats_mut();
                stats.view_no_children_joins.num_joins += 1;
                if completed {
                    stats.view_no_children_joins.completed_joins += 1;
                }
                stats.view_no_children_joins.vars_reduced += num_vars;
            }
            (false, false) => {
                let mut parents = target_ctx.parent_list(self).unwrap();
                parents.reverse();
                parents.push(target_ctx);
                let vars_reduced = parents.iter().fold(0, |mut acc, ctx| {
                    acc += ctx.vars(self).len();
                    acc
                });
                let stats = self.join_stats_mut();
                stats.view_children_no_forks_joins.num_joins += 1;
                if completed {
                    stats.view_children_no_forks_joins.completed_joins += 1;
                }
                // parents is now: [body_ctx, ..., edges[0]]
                stats.view_children_no_forks_joins.vars_reduced += vars_reduced;
            }
            (false, true) => {
                let stats = self.join_stats_mut();
                stats.view_children_forks_joins.num_joins += 1;
                if completed {
                    stats.view_children_forks_joins.completed_joins += 1;
                }
            }
        }
    }

    fn add_completed_mut(
        &mut self,
        completed: bool,
        no_children: bool,
        forks: bool,
        target_ctx: ContextNode,
    ) where
        Self: Sized + GraphBackend,
    {
        match (no_children, forks) {
            (true, _) => {
                let num_vars = target_ctx.vars(self).len();
                let stats = self.join_stats_mut();
                stats.mut_no_children_joins.num_joins += 1;
                if completed {
                    stats.mut_no_children_joins.completed_joins += 1;
                }
                stats.mut_no_children_joins.vars_reduced += num_vars;
            }
            (false, false) => {
                let stats = self.join_stats_mut();
                stats.mut_children_no_forks_joins.num_joins += 1;
                if completed {
                    stats.mut_children_no_forks_joins.completed_joins += 1;
                }
            }
            (false, true) => {
                let stats = self.join_stats_mut();
                stats.mut_children_forks_joins.num_joins += 1;
                if completed {
                    stats.mut_children_forks_joins.completed_joins += 1;
                }
            }
        }
    }
}
