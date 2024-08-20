use crate::helper::CallerHelper;
use crate::Flatten;
use graph::nodes::CallFork;
use graph::RangeEval;

use graph::{
    elem::{Elem, RangeElem},
    nodes::{Concrete, ContextNode, ContextVarNode, ContractNode, ExprRet, FuncVis, FunctionNode},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Range, SolcRange,
};
use shared::{AnalyzerLike, ExprErr, GraphError, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Loc};

use std::collections::{BTreeMap, BTreeSet};

impl<T> FuncApplier for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>
        + Sized
        + GraphBackend
        + CallerHelper
        + ApplyStatTracker
{
}

pub struct ApplyInputs<'a> {
    /// Variables passed into the function
    pub func_inputs: &'a [ContextVarNode],
    /// Storage variables to be used in the function
    pub storage_inputs: Option<&'a [ContextVarNode]>,
    /// Environment variables (msg.sender, etc) to be used in the function
    pub env_inputs: Option<&'a [ContextVarNode]>,
}

#[derive(Debug, Copy, Clone)]
pub struct ApplyContexts {
    /// The context to place the return variables into
    pub target_ctx: ContextNode,
    /// The first context for the function that is to be applied
    pub genesis_func_ctx: ContextNode,
    /// The final context of the function that is to be applied (i.e. if genesis_func_ctx has subcontexts)
    pub result_func_ctx: ContextNode,
}

impl ApplyContexts {
    pub fn storage_inputs(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<BTreeMap<ContractNode, BTreeSet<ContextVarNode>>, GraphError> {
        let mut accumulated_vars = Default::default();
        Self::recursive_storage_inputs(analyzer, self.target_ctx, &mut accumulated_vars)?;
        Ok(accumulated_vars)
    }

    /// Walk up the context tree accumulating all accessed storage variables
    pub fn recursive_storage_inputs(
        analyzer: &mut impl AnalyzerBackend,
        ctx: ContextNode,
        accumulated_vars: &mut BTreeMap<ContractNode, BTreeSet<ContextVarNode>>,
    ) -> Result<(), GraphError> {
        if let Some(contract) = ctx.maybe_associated_contract(analyzer)? {
            ctx.storage_vars(analyzer).iter().for_each(|var| {
                let entry = accumulated_vars.entry(contract).or_default();
                entry.insert(var.global_first_version(analyzer));
            });
        }

        if let Some(parent) = ctx.underlying(analyzer)?.parent_ctx() {
            Self::recursive_storage_inputs(analyzer, parent, accumulated_vars)?;
        }
        Ok(())
    }

    pub fn basic_params(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<BTreeMap<usize, Vec<ContextVarNode>>, GraphError> {
        let fn_param_names = self
            .genesis_func_ctx
            .associated_fn(analyzer)
            .unwrap()
            .ordered_param_names(analyzer);
        let mut res: BTreeMap<usize, Vec<ContextVarNode>> = Default::default();
        self.genesis_func_ctx
            .input_variables(analyzer)
            .iter()
            .try_for_each(|var| {
                let var_name = var.name(analyzer).unwrap();
                let pos = fn_param_names
                    .iter()
                    .position(|ordered_name| var_name == *ordered_name)
                    .unwrap();
                let mut vars = vec![*var];
                vars.extend(var.fielded_to_fields(analyzer)?);
                res.insert(pos, vars);
                Ok(())
            })?;
        Ok(res)
    }

    /// Walk down the context tree from the application function context to find all needed storage variables
    pub fn storage_params(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<BTreeMap<ContractNode, BTreeSet<ContextVarNode>>, GraphError> {
        let mut accumulated_vars = Default::default();
        Self::recursive_storage_params(analyzer, self.genesis_func_ctx, &mut accumulated_vars)?;
        Ok(accumulated_vars)
    }

    fn recursive_storage_params(
        analyzer: &mut impl AnalyzerBackend,
        ctx: ContextNode,
        accumulated_vars: &mut BTreeMap<ContractNode, BTreeSet<ContextVarNode>>,
    ) -> Result<(), GraphError> {
        if let Some(contract) = ctx.maybe_associated_contract(analyzer)? {
            ctx.storage_vars(analyzer).iter().for_each(|var| {
                let entry = accumulated_vars.entry(contract).or_default();
                entry.insert(var.global_first_version(analyzer));
            });
        }

        if let Some(child) = ctx.underlying(analyzer)?.child {
            match child {
                CallFork::Call(c) => {
                    Self::recursive_storage_params(analyzer, c, accumulated_vars)?;
                }
                CallFork::Fork(w1, w2) => {
                    Self::recursive_storage_params(analyzer, w1, accumulated_vars)?;
                    Self::recursive_storage_params(analyzer, w2, accumulated_vars)?;
                }
            }
        }
        Ok(())
    }

    pub fn generate_replacement_map(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        inputs: &[ContextVarNode],
        func_mut: FuncVis,
    ) -> Result<BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>, GraphError> {
        let mut mapping: BTreeMap<_, _> = Default::default();
        let basic_map = self.basic_params(analyzer)?;
        basic_map.iter().try_for_each(|(i, params)| {
            let input = inputs[*i].latest_version(analyzer);
            if params.len() == 1 {
                let elem = Elem::from(input).cast(Elem::from(params[0]));
                mapping.insert(params[0].0.into(), (elem, input));
            } else {
                let mut param_iter = params.iter();
                let elem = Elem::from(input).cast(Elem::from(params[0]));
                mapping.insert(param_iter.next().unwrap().0.into(), (elem, input));
                for param_field in param_iter {
                    let maybe_input_field = input.find_field(
                        analyzer,
                        &param_field
                            .maybe_field_name(analyzer)
                            .unwrap()
                            .expect("expected this to be field name"),
                    )?;
                    let input_field = maybe_input_field.expect("expected to have matching field");
                    let elem = Elem::from(input_field).cast(Elem::from(*param_field));
                    mapping.insert(param_field.0.into(), (elem, input_field));
                }
            }
            Ok(())
        })?;
        match func_mut {
            FuncVis::Pure => {
                // nothing else to do
            }
            FuncVis::View => {
                todo!()
            }
            FuncVis::Mut => {
                todo!()
            }
        }
        Ok(mapping)
    }

    pub fn generate_basic_return_vars(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<(ContextVarNode, bool)>, GraphError> {
        Ok(self
            .result_func_ctx
            .return_nodes(analyzer)?
            .iter()
            .enumerate()
            .flat_map(|(i, ret)| {
                let func_name = self
                    .genesis_func_ctx
                    .associated_fn(analyzer)
                    .unwrap()
                    .loc_specified_name(analyzer)
                    .unwrap();
                let mut new_var = ret.var().underlying(analyzer).unwrap().clone();
                let new_name = format!(
                    "tmp_{}({func_name}.{i})",
                    self.target_ctx.new_tmp(analyzer).unwrap(),
                );
                new_var.name.clone_from(&new_name);
                new_var.display_name = new_name.clone();
                if let Some(mut range) = new_var.ty.take_range() {
                    range.min = range.min.simplify_minimize(analyzer, arena).unwrap();
                    range.max = range.max.simplify_maximize(analyzer, arena).unwrap();
                    new_var.ty.set_range(range).unwrap();
                }
                let new_cvar = ContextVarNode::from(analyzer.add_node(new_var));
                analyzer.add_edge(
                    new_cvar,
                    self.target_ctx,
                    Edge::Context(ContextEdge::Variable),
                );
                self.target_ctx.add_var(new_cvar, analyzer).unwrap();
                if let Ok(fields) = ret.var().fielded_to_fields(analyzer) {
                    if !fields.is_empty() {
                        let mut vars = fields
                            .iter()
                            .map(|field| {
                                let mut new_field_var = field.underlying(analyzer).unwrap().clone();
                                let new_name =
                                    format!("{func_name}.{i}.{}", field.name(analyzer).unwrap());
                                new_field_var.name.clone_from(&new_name);
                                new_field_var.display_name = new_name;
                                let new_field =
                                    ContextVarNode::from(analyzer.add_node(new_field_var));
                                analyzer.add_edge(
                                    new_field,
                                    new_cvar,
                                    Edge::Context(ContextEdge::AttrAccess("field")),
                                );
                                (new_field, false)
                            })
                            .collect::<Vec<_>>();
                        vars.push((new_cvar, true));
                        vars
                    } else {
                        vec![(new_cvar, true)]
                    }
                } else {
                    vec![(new_cvar, true)]
                }
            })
            .collect::<Vec<_>>())
    }

    pub fn update_var(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        replacement_map: &BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>,
        var: ContextVarNode,
    ) -> Result<(), GraphError> {
        let new_name = var.display_name(analyzer).unwrap();
        tracing::trace!("handling apply range update: {new_name}");

        // update the vars range
        if let Some(mut range) = var.ty_mut(analyzer)?.take_range() {
            println!(
                "og range: [{:#?},{:#?}]",
                range.min.recurse_dearenaize(arena),
                range.max.recurse_dearenaize(arena)
            );
            let mut range: SolcRange = range.take_flattened_range(analyzer, arena).unwrap().into();
            println!(
                "flat range: [{:#?},{:#?}]",
                range.min.recurse_dearenaize(arena),
                range.max.recurse_dearenaize(arena)
            );
            // use the replacement map
            replacement_map
                .iter()
                .try_for_each(|(replace, replacement)| {
                    range.replace_dep(*replace, replacement.0.clone(), analyzer, arena)
                })?;
            println!(
                "replace range: [{:#?},{:#?}]",
                range.min.recurse_dearenaize(arena),
                range.max.recurse_dearenaize(arena)
            );
            range.cache_eval(analyzer, arena).unwrap();
            println!(
                "eval range: [{:#?},{:#?}]",
                range.min.recurse_dearenaize(arena),
                range.max.recurse_dearenaize(arena)
            );
            var.set_range(analyzer, range).unwrap();
        }

        // update the vars dep_on
        if let Some(ref mut dep_on) = var.underlying_mut(analyzer)?.dep_on {
            dep_on.iter_mut().for_each(|d| {
                if let Some((_, r)) = replacement_map.get(&(*d).into()) {
                    *d = *r
                }
            });
        }

        Ok(())
    }

    pub fn add_deps(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        replacement_map: &BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>,
    ) -> Result<bool, GraphError> {
        let mut unsat = false;
        self.result_func_ctx
            .ctx_deps(analyzer)?
            .iter()
            .try_for_each(|dep| {
                let new_var = dep.underlying(analyzer)?.clone();
                let new_cvar = ContextVarNode::from(analyzer.add_node(new_var));
                self.update_var(analyzer, arena, replacement_map, new_cvar)?;
                analyzer.add_edge(
                    new_cvar,
                    self.target_ctx,
                    Edge::Context(ContextEdge::Variable),
                );
                self.target_ctx.add_ctx_dep(new_cvar, analyzer, arena)?;
                if let Some(r) = new_cvar.range(analyzer)? {
                    unsat |= r.unsat(analyzer, arena);
                }
                Ok(())
            })?;
        Ok(unsat)
    }

    pub fn apply_replacement_map(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        map: &BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>,
        func_mut: FuncVis,
    ) -> Result<ExprRet, GraphError> {
        let ret_vars = self.generate_basic_return_vars(analyzer, arena)?;
        ret_vars
            .iter()
            .try_for_each(|(ret_var, _)| self.update_var(analyzer, arena, map, *ret_var))?;
        // TODO: handle unsat
        let _ = self.add_deps(analyzer, arena, map)?;

        match func_mut {
            FuncVis::Pure => {
                // nothing more to do
                Ok(ExprRet::Multi(
                    ret_vars
                        .into_iter()
                        .filter_map(|(var, real_ret)| {
                            if real_ret {
                                Some(ExprRet::from(var))
                            } else {
                                None
                            }
                        })
                        .collect(),
                ))
            }
            FuncVis::View => {
                todo!("view")
            }
            FuncVis::Mut => {
                todo!("mut")
            }
        }
    }

    pub fn apply(
        &mut self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        inputs: &[ContextVarNode],
    ) -> Result<bool, GraphError> {
        match self
            .genesis_func_ctx
            .associated_fn(analyzer)
            .unwrap()
            .visibility(analyzer)
            .unwrap()
        {
            FuncVis::Mut => {
                return Ok(false);
            }
            FuncVis::View => {
                return Ok(false);
            }
            _ => {}
        }
        if self.genesis_func_ctx.underlying(analyzer)?.child.is_some() {
            // potentially multi-edge
            Ok(false)
        } else {
            // single edge
            self.result_func_ctx = self.genesis_func_ctx;
            let func_mut = self
                .genesis_func_ctx
                .associated_fn(analyzer)?
                .visibility(analyzer)?;
            let map = self.generate_replacement_map(analyzer, inputs, func_mut)?;
            println!("replacement map: {:#?}", map);
            let res = self.apply_replacement_map(analyzer, arena, &map, func_mut)?;
            self.target_ctx.push_expr(res, analyzer)?;
            Ok(true)
        }
    }
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
        func_inputs: &[ContextVarNode],
        seen: &mut Vec<FunctionNode>,
    ) -> Result<bool, ExprErr> {
        tracing::trace!(
            "Trying to apply function: {} onto context {}",
            func.loc_specified_name(self).into_expr_err(loc)?,
            ctx.path(self)
        );

        let mut ctxs = ApplyContexts {
            target_ctx: ctx,
            genesis_func_ctx: ContextNode(0),
            result_func_ctx: ContextNode(0),
        };

        if let Some(apply_ctx) = func.maybe_body_ctx(self) {
            ctxs.genesis_func_ctx = apply_ctx;
        } else {
            if ctx.associated_fn(self) == Ok(func) {
                return Ok(false);
            }

            if seen.contains(&func) {
                return Ok(false);
            }

            self.handled_funcs_mut().push(func);
            if func.underlying(self).unwrap().body.is_some() {
                self.interpret_entry_func(func, arena);
            }

            seen.push(func);
            if let Some(body_ctx) = func.maybe_body_ctx(self) {
                ctxs.genesis_func_ctx = body_ctx;
            } else {
                return Ok(false);
            }
        }

        ctxs.apply(self, arena, func_inputs).into_expr_err(loc)
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
