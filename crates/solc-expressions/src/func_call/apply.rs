use crate::helper::CallerHelper;
use crate::member_access::ListAccess;
use crate::variable::Variable;
use crate::Flatten;
use solang_parser::helpers::CodeLocation;

use graph::{
    elem::{Elem, RangeElem, RangeExpr, RangeOp},
    nodes::{
        Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, FuncVis, FunctionNode,
        FunctionParamNode, KilledKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, Range, SolcRange, VarType,
};
use shared::{AnalyzerLike, ExprErr, IntoExprErr, NodeIdx, RangeArena, StorageLocation};

use solang_parser::pt::{Expression, Loc};

use std::collections::BTreeMap;

impl<T> FuncApplier for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>
        + Sized
        + GraphBackend
        + CallerHelper
        + ApplyStatTracker
{
}
/// A trait for calling a function
pub trait FuncApplier:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ApplyStatTracker
{
    #[tracing::instrument(level = "trace", skip_all)]
    fn apply(
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
            "Trying to apply function: {} onto context {}",
            func.loc_specified_name(self).into_expr_err(loc)?,
            ctx.path(self)
        );
        // ensure no modifiers (for now)
        // if pure function:
        //      grab requirements for context
        //      grab return node's simplified range
        //      replace fundamentals with function inputs
        //      update ctx name in place
        //
        match func.visibility(self).into_expr_err(loc)? {
            FuncVis::Pure => {
                // pure functions are guaranteed to not require the use of state, so
                // the only things we care about are function inputs and function outputs
                if let Some(apply_ctx) = func.maybe_body_ctx(self) {
                    if apply_ctx
                        .underlying(self)
                        .into_expr_err(loc)?
                        .child
                        .is_some()
                    {
                        tracing::trace!(
                            "Applying function: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        let edges = apply_ctx.successful_edges(self).into_expr_err(loc)?;
                        match edges.len() {
                            0 => {
                                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                            }
                            1 => {
                                if !self.apply_pure(
                                    arena,
                                    loc,
                                    func,
                                    params,
                                    func_inputs,
                                    apply_ctx,
                                    edges[0],
                                    ctx,
                                    false,
                                )? {
                                    ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                                }
                                return Ok(true);
                            }
                            2.. => {
                                tracing::trace!(
                                    "Branching pure apply function: {}",
                                    func.name(self).into_expr_err(loc)?
                                );
                                // self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                                let new_forks =
                                    ctx.set_apply_forks(loc, edges.clone(), self).unwrap();
                                edges.into_iter().zip(new_forks.iter()).try_for_each(
                                    |(edge, new_fork)| {
                                        let res = self.apply_pure(
                                            arena,
                                            loc,
                                            func,
                                            params,
                                            func_inputs,
                                            apply_ctx,
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
                            "Childless pure apply: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        let res = self.apply_pure(
                            arena,
                            loc,
                            func,
                            params,
                            func_inputs,
                            apply_ctx,
                            apply_ctx,
                            ctx,
                            false,
                        )?;
                        if !res {
                            ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
                        }
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
                        self.traverse_statement(&body, None);
                        self.interpret(func, body.loc(), arena)
                    }

                    seen.push(func);
                    return self.apply(arena, ctx, loc, func, params, func_inputs, seen);
                }
            }
            FuncVis::View => {
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
                                "View apply function: {}",
                                func.name(self).into_expr_err(loc)?
                            );
                            self.add_completed_view(false, false, false, body_ctx);
                        } else {
                            tracing::trace!(
                                "Branching view apply function: {}",
                                func.name(self).into_expr_err(loc)?
                            );
                            self.add_completed_view(false, false, true, body_ctx);
                        }
                    } else {
                        tracing::trace!(
                            "Childless view apply function: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        self.add_completed_view(false, true, false, body_ctx);
                    }
                } else {
                    tracing::trace!("View function not processed");
                    if ctx.associated_fn(self) == Ok(func) {
                        return Ok(false);
                    }

                    if seen.contains(&func) {
                        return Ok(false);
                    }

                    self.handled_funcs_mut().push(func);
                    if let Some(body) = &func.underlying(self).unwrap().body.clone() {
                        self.traverse_statement(&body, None);
                        self.interpret(func, body.loc(), arena)
                    }

                    seen.push(func);
                }
            }
            FuncVis::Mut => {
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
                                "Mut apply function: {}",
                                func.name(self).into_expr_err(loc)?
                            );
                            self.add_completed_mut(false, false, false, body_ctx);
                        } else {
                            tracing::trace!(
                                "Branching mut apply function: {}",
                                func.name(self).into_expr_err(loc)?
                            );
                            self.add_completed_mut(false, false, true, body_ctx);
                        }
                    } else {
                        tracing::trace!(
                            "Childless mut apply function: {}",
                            func.name(self).into_expr_err(loc)?
                        );
                        self.add_completed_mut(false, true, false, body_ctx);
                    }
                } else {
                    tracing::trace!("Mut function not processed");
                    if ctx.associated_fn(self) == Ok(func) {
                        return Ok(false);
                    }

                    if seen.contains(&func) {
                        return Ok(false);
                    }

                    self.handled_funcs_mut().push(func);
                    if let Some(body) = &func.underlying(self).unwrap().body.clone() {
                        self.traverse_statement(&body, None);
                        self.interpret(func, body.loc(), arena)
                    }

                    seen.push(func);
                }
            }
        }

        Ok(false)
    }

    fn apply_pure(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        func: FunctionNode,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
        apply_ctx: ContextNode,
        resulting_edge: ContextNode,
        target_ctx: ContextNode,
        forks: bool,
    ) -> Result<bool, ExprErr> {
        // construct remappings for inputs
        // if applying func a(uint x), map will be <x, (replacement_elem, replacement_idx)
        //
        // fucntion a(uint x) returns (uint y) {
        //    y = x + 5;
        // }
        //  y will be returned and relies on x - therefore we need to replace all references of
        //  x using the replacement map
        //
        //  What is produced is a ContextVarNode that's range is like the return of the normal function
        //  but with x replaced with the input provided
        tracing::trace!("here");
        let replacement_map = self.basic_inputs_replacement_map(
            arena,
            apply_ctx,
            target_ctx,
            loc,
            params,
            func_inputs,
        )?;
        tracing::trace!("applying pure function - replacement map: {replacement_map:#?}");
        let mut rets: Vec<_> = resulting_edge
            .return_nodes(self)
            .into_expr_err(loc)?
            .iter()
            .enumerate()
            .map(|(i, (_, ret_node))| {
                let mut new_var = ret_node.underlying(self).unwrap().clone();
                let new_name = format!("{}.{i}", func.loc_specified_name(self).unwrap());
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
                                func.loc_specified_name(self).unwrap(),
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

        let new_path = format!(
            "{}.{}.resume{{ {} }}",
            target_ctx.path(self),
            resulting_edge.path(self),
            target_ctx.associated_fn_name(self).unwrap()
        );
        let underlying_mut = target_ctx.underlying_mut(self).into_expr_err(loc)?;
        underlying_mut.path = new_path;

        target_ctx
            .propogate_applied(func, self)
            .into_expr_err(loc)?;
        if let Some(body) = func.maybe_body_ctx(self) {
            for app in body.underlying(self).into_expr_err(loc)?.applies.clone() {
                target_ctx.propogate_applied(app, self).into_expr_err(loc)?;
            }
        }

        target_ctx
            .push_expr(ExprRet::Multi(rets), self)
            .into_expr_err(loc)?;
        self.add_completed_pure(true, false, forks, resulting_edge);
        Ok(true)
    }

    fn basic_inputs_replacement_map(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        apply_ctx: ContextNode,
        target_ctx: ContextNode,
        loc: Loc,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
    ) -> Result<BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>, ExprErr> {
        let inputs = apply_ctx.input_variables(self);
        let mut replacement_map: BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)> =
            BTreeMap::default();
        params
            .iter()
            .zip(func_inputs.iter())
            .try_for_each(|(param, func_input)| {
                if let Some(name) = param.maybe_name(self).into_expr_err(loc)? {
                    let mut new_cvar = func_input
                        .latest_version_or_inherited_in_ctx(apply_ctx, self)
                        .underlying(self)
                        .into_expr_err(loc)?
                        .clone();
                    new_cvar.loc = Some(param.loc(self).unwrap());
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
                        target_ctx,
                        Edge::Context(ContextEdge::Variable),
                    );
                    target_ctx.add_var(replacement, self);

                    if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self).unwrap()) {
                        if !replacement.ty_eq_ty(&param_ty, self).into_expr_err(loc)? {
                            replacement
                                .cast_from_ty(param_ty, self, arena)
                                .into_expr_err(loc)?;
                        }
                    }

                    if let Some(_len_var) = replacement.array_to_len_var(self) {
                        // bring the length variable along as well
                        self.get_length(arena, apply_ctx, loc, *func_input, false)
                            .unwrap();
                    }

                    if let (Some(r), Some(r2)) =
                        (replacement.range(self).unwrap(), param.range(self).unwrap())
                    {
                        let new_min = r.range_min().into_owned().cast(r2.range_min().into_owned());
                        let new_max = r.range_max().into_owned().cast(r2.range_max().into_owned());
                        replacement
                            .latest_version_or_inherited_in_ctx(apply_ctx, self)
                            .try_set_range_min(self, arena, new_min)
                            .into_expr_err(loc)?;
                        replacement
                            .latest_version_or_inherited_in_ctx(apply_ctx, self)
                            .try_set_range_max(self, arena, new_max)
                            .into_expr_err(loc)?;
                        replacement
                            .latest_version_or_inherited_in_ctx(apply_ctx, self)
                            .try_set_range_exclusions(self, r.exclusions)
                            .into_expr_err(loc)?;
                    }

                    let Some(correct_input) = inputs
                        .iter()
                        .find(|input| input.name(self).unwrap() == name)
                    else {
                        return Err(ExprErr::InvalidFunctionInput(
                            loc,
                            "Could not match input to parameter".to_string(),
                        ));
                    };

                    let target_fields = correct_input.struct_to_fields(self).into_expr_err(loc)?;
                    let replacement_fields =
                        func_input.struct_to_fields(self).into_expr_err(loc)?;
                    let match_field =
                        |this: &Self,
                         target_field: ContextVarNode,
                         replacement_fields: &[ContextVarNode]|
                         -> Option<(ContextVarNode, ContextVarNode)> {
                            let target_full_name = target_field.name(this).clone().unwrap();
                            let target_field_name = target_full_name
                                .split('.')
                                .collect::<Vec<_>>()
                                .last()
                                .cloned()
                                .unwrap();
                            let replacement_field =
                                replacement_fields.iter().find(|rep_field| {
                                    let replacement_full_name = rep_field.name(this).unwrap();
                                    let replacement_field_name = replacement_full_name
                                        .split('.')
                                        .collect::<Vec<_>>()
                                        .last()
                                        .cloned()
                                        .unwrap();
                                    replacement_field_name == target_field_name
                                })?;
                            Some((target_field, *replacement_field))
                        };

                    let mut struct_stack = target_fields
                        .into_iter()
                        .filter_map(|i| match_field(self, i, &replacement_fields[..]))
                        .collect::<Vec<_>>();

                    while let Some((target_field, replacement_field)) = struct_stack.pop() {
                        let mut replacement_field_as_elem = Elem::from(replacement_field);
                        replacement_field_as_elem.arenaize(self, arena).unwrap();
                        let to_replace = target_field.next_version(self).unwrap_or(target_field);
                        replacement_map.insert(
                            to_replace.0.into(),
                            (replacement_field_as_elem.clone(), replacement_field),
                        );

                        let target_sub_fields =
                            target_field.struct_to_fields(self).into_expr_err(loc)?;
                        let replacement_sub_fields = replacement_field
                            .struct_to_fields(self)
                            .into_expr_err(loc)?;
                        let subs = target_sub_fields
                            .into_iter()
                            .filter_map(|i| match_field(self, i, &replacement_sub_fields[..]))
                            .collect::<Vec<_>>();
                        struct_stack.extend(subs);
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

impl<T> ApplyStatTracker for T where T: AnalyzerLike + GraphBackend {}

pub trait ApplyStatTracker: AnalyzerLike {
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
                let stats = self.apply_stats_mut();
                stats.pure_no_children_applies.num_applies += 1;
                if completed {
                    stats.pure_no_children_applies.completed_applies += 1;
                }
                stats.pure_no_children_applies.vars_reduced += num_vars;
            }
            (false, false) => {
                let mut parents = target_ctx.parent_list(self).unwrap();
                parents.reverse();
                parents.push(target_ctx);
                let vars_reduced = parents.iter().fold(0, |mut acc, ctx| {
                    acc += ctx.vars(self).len();
                    acc
                });
                let stats = self.apply_stats_mut();
                stats.pure_children_no_forks_applies.num_applies += 1;
                if completed {
                    stats.pure_children_no_forks_applies.completed_applies += 1;
                }
                stats.pure_children_no_forks_applies.vars_reduced += vars_reduced;
            }
            (false, true) => {
                let stats = self.apply_stats_mut();
                stats.pure_children_forks_applies.num_applies += 1;
                if completed {
                    stats.pure_children_forks_applies.completed_applies += 1;
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
                let stats = self.apply_stats_mut();
                stats.view_no_children_applies.num_applies += 1;
                if completed {
                    stats.view_no_children_applies.completed_applies += 1;
                }
                stats.view_no_children_applies.vars_reduced += num_vars;
            }
            (false, false) => {
                let mut parents = target_ctx.parent_list(self).unwrap();
                parents.reverse();
                parents.push(target_ctx);
                let vars_reduced = parents.iter().fold(0, |mut acc, ctx| {
                    acc += ctx.vars(self).len();
                    acc
                });
                let stats = self.apply_stats_mut();
                stats.view_children_no_forks_applies.num_applies += 1;
                if completed {
                    stats.view_children_no_forks_applies.completed_applies += 1;
                }
                // parents is now: [body_ctx, ..., edges[0]]
                stats.view_children_no_forks_applies.vars_reduced += vars_reduced;
            }
            (false, true) => {
                let stats = self.apply_stats_mut();
                stats.view_children_forks_applies.num_applies += 1;
                if completed {
                    stats.view_children_forks_applies.completed_applies += 1;
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
                let stats = self.apply_stats_mut();
                stats.mut_no_children_applies.num_applies += 1;
                if completed {
                    stats.mut_no_children_applies.completed_applies += 1;
                }
                stats.mut_no_children_applies.vars_reduced += num_vars;
            }
            (false, false) => {
                let stats = self.apply_stats_mut();
                stats.mut_children_no_forks_applies.num_applies += 1;
                if completed {
                    stats.mut_children_no_forks_applies.completed_applies += 1;
                }
            }
            (false, true) => {
                let stats = self.apply_stats_mut();
                stats.mut_children_forks_applies.num_applies += 1;
                if completed {
                    stats.mut_children_forks_applies.completed_applies += 1;
                }
            }
        }
    }
}
