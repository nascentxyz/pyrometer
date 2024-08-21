use crate::helper::CallerHelper;
use crate::{Flatten, Variable};
use graph::nodes::{CallFork, KilledKind};
use graph::RangeEval;

use graph::{
    elem::{Elem, RangeElem},
    nodes::{
        Concrete, ContextNode, ContextVar, ContextVarNode, ContractNode, ExprRet, FuncVis,
        FunctionNode,
    },
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

    /// Recursively collects storage parameters from the context tree.
    ///
    /// This function traverses the context tree, starting from the given context,
    /// and accumulates all storage variables encountered. It handles both single
    /// contexts and forked contexts (multiple execution paths).
    ///
    /// # Arguments
    ///
    /// * `analyzer` - A mutable reference to the analyzer backend.
    /// * `ctx` - The current context node being processed.
    /// * `accumulated_vars` - A mutable reference to a map that accumulates
    ///   storage variables, grouped by contract.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success (`Ok(())`) or a `GraphError` if an error occurs.
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

    /// Generates a replacement map for function application.
    ///
    /// This method creates a mapping between the function parameters and the provided input variables.
    /// It handles both simple and complex (fielded) parameters.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `inputs` - The input variables to be mapped to function parameters.
    /// * `func_mut` - The mutability of the function being applied.
    ///
    /// # Returns
    ///
    /// A `Result` containing a `BTreeMap` that maps `NodeIdx` to a tuple of `(Elem<Concrete>, ContextVarNode)`,
    /// or a `GraphError` if an error occurs during the process.
    ///
    /// # Errors
    ///
    /// This function will return an error if there are issues accessing or manipulating the graph structure.
    pub fn generate_replacement_map(
        &self,
        analyzer: &mut impl Variable,
        arena: &mut RangeArena<Elem<Concrete>>,
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
                // TODO: handle fielded storage
                // TODO: handle env vars
                let storage_params = self.storage_params(analyzer)?;
                let storage_inputs = self.storage_inputs(analyzer)?;

                for (contract, params) in storage_params.iter() {
                    // for each storage param, make sure we have it in storage inputs
                    let missing_params = if let Some(contract_inputs) = storage_inputs.get(contract)
                    {
                        let mut diff: BTreeSet<_> = Default::default();
                        for param in params {
                            let Ok(param_name) = param.name(analyzer) else {
                                continue;
                            };
                            if !contract_inputs
                                .iter()
                                .any(|input| input.name(analyzer).as_ref() == Ok(&param_name))
                            {
                                diff.insert(*param);
                            }
                        }
                        diff
                    } else {
                        params.clone()
                    };
                    for missing_param in missing_params {
                        let Ok(param_name) = missing_param.name(analyzer) else {
                            continue;
                        };

                        if self.target_ctx.maybe_associated_contract(analyzer)? == Some(*contract) {
                            if analyzer
                                .contract_variable(
                                    arena,
                                    self.target_ctx,
                                    *contract,
                                    param_name,
                                    Loc::Implicit,
                                )
                                .is_err()
                            {
                                continue;
                            }
                        } else {
                            todo!();
                        }
                    }
                }

                let storage_inputs = self.storage_inputs(analyzer)?;
                for (contract, params) in storage_params {
                    if let Some(contract_inputs) = storage_inputs.get(&contract) {
                        for param in params {
                            let Ok(param_name) = param.name(analyzer) else {
                                continue;
                            };
                            if let Some(input) = contract_inputs.iter().find(|&input| {
                                let Ok(i_name) = input.name(analyzer) else {
                                    return false;
                                };
                                i_name == param_name
                            }) {
                                let latest_input = input.latest_version(analyzer);
                                let elem = Elem::from(latest_input).cast(Elem::from(param));
                                let overwrite =
                                    mapping.insert(param.0.into(), (elem, latest_input));
                                assert!(overwrite.is_none());
                            } else {
                                println!("couldnt find {param_name} used in caller");
                                // the context didnt have all the used storage, bring it in
                            }
                        }
                    }
                }
            }
            FuncVis::Mut => {
                todo!()
            }
        }
        Ok(mapping)
    }

    /// Generates basic return variables for the function application.
    ///
    /// This method creates new context variables in the target context to represent
    /// the return values of the applied function. It handles both single and multi-field
    /// return types.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `arena` - The range arena for element storage.
    ///
    /// # Returns
    ///
    /// A `Result` containing a vector of tuples. Each tuple contains:
    /// - A `ContextVarNode` representing a return variable.
    /// - A boolean indicating whether this is a real return value (true) or a field of a struct return value (false).
    ///
    /// # Errors
    ///
    /// Returns a `GraphError` if any graph operations fail.
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

    /// Updates a variable in the context based on the replacement map.
    ///
    /// This method updates the range and dependencies of a given context variable
    /// using the provided replacement map.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `arena` - The range arena for element storage.
    /// * `replacement_map` - A map of node indices to their replacements.
    /// * `var` - The context variable to be updated.
    ///
    /// # Returns
    ///
    /// A `Result` indicating success or a `GraphError` if an error occurs.
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
            let mut range: SolcRange = range.take_flattened_range(analyzer, arena).unwrap().into();
            // use the replacement map
            replacement_map
                .iter()
                .try_for_each(|(replace, replacement)| {
                    range.replace_dep(*replace, replacement.0.clone(), analyzer, arena)
                })?;
            range.cache_eval(analyzer, arena).unwrap();
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

    /// Adds dependencies to the target context based on the result function context.
    ///
    /// This method processes the context dependencies from the result function context,
    /// updates them using the replacement map, and adds them to the target context.
    /// It also checks for unsatisfiable conditions during this process.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `arena` - The range arena for element storage.
    /// * `replacement_map` - A map of node indices to their replacements.
    ///
    /// # Returns
    ///
    /// A `Result` containing a boolean indicating whether an unsatisfiable condition was encountered,
    /// or a `GraphError` if an error occurs during the process.
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
                    if let Ok(max) = r.evaled_range_max(analyzer, arena) {
                        if let Some(conc) = max.maybe_concrete() {
                            unsat |= matches!(conc.val, Concrete::Bool(false));
                        }
                    }
                    unsat |= r.unsat(analyzer, arena);
                }
                Ok(())
            })?;
        Ok(unsat)
    }

    /// Applies the replacement map to update the context and generate return values.
    ///
    /// This method processes the replacement map, updates the context variables,
    /// and generates return values based on the function's mutability.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `arena` - The range arena for element storage.
    /// * `map` - The replacement map containing node replacements.
    /// * `func_mut` - The mutability of the function being applied.
    ///
    /// # Returns
    ///
    /// A `Result` containing an `Option<ExprRet>`. The `Option` is `None` if the
    /// application results in an unsatisfiable condition, otherwise it contains
    /// the function's return value(s).
    ///
    /// # Errors
    ///
    /// Returns a `GraphError` if any graph operations fail during the process.
    pub fn apply_replacement_map(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        map: &BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>,
        func_mut: FuncVis,
    ) -> Result<Option<ExprRet>, GraphError> {
        let ret_vars = self.generate_basic_return_vars(analyzer, arena)?;
        ret_vars
            .iter()
            .try_for_each(|(ret_var, _)| self.update_var(analyzer, arena, map, *ret_var))?;

        match func_mut {
            FuncVis::Pure => {
                if self.add_deps(analyzer, arena, map)? {
                    return Ok(None);
                }
                analyzer.add_completed_pure(true, true, false, self.target_ctx);
                Ok(Some(ExprRet::Multi(
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
                )))
            }
            FuncVis::View => {
                if self.add_deps(analyzer, arena, map)? {
                    return Ok(None);
                }

                analyzer.add_completed_view(true, true, false, self.target_ctx);

                Ok(Some(ExprRet::Multi(
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
                )))
            }
            FuncVis::Mut => {
                // TODO:
                todo!("mut")
            }
        }
    }

    /// Applies a function to the given context with the provided inputs.
    ///
    /// This method handles the application of a function to a specific context,
    /// updating the context and generating return values based on the function's
    /// behavior and mutability.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - The analyzer backend used for graph operations.
    /// * `arena` - The range arena for element storage.
    /// * `inputs` - A slice of `ContextVarNode` representing the function inputs.
    /// * `loc` - The location information for error reporting.
    ///
    /// # Returns
    ///
    /// A `Result` containing a boolean indicating whether the application was
    /// successful (true) or not (false), or a `GraphError` if an error occurred.
    pub fn apply(
        &mut self,
        analyzer: &mut (impl AnalyzerBackend + Variable),
        arena: &mut RangeArena<Elem<Concrete>>,
        inputs: &[ContextVarNode],
        loc: Loc,
    ) -> Result<bool, GraphError> {
        let func_mut = self
            .genesis_func_ctx
            .associated_fn(analyzer)?
            .visibility(analyzer)?;

        if func_mut == FuncVis::Mut {
            return Ok(false);
        }

        let edges = if self.genesis_func_ctx.underlying(analyzer)?.child.is_some() {
            self.genesis_func_ctx.successful_edges(analyzer)?
        } else {
            vec![self.genesis_func_ctx]
        };
        match edges.len() {
            0 => {
                // always reverts
                self.target_ctx.kill(analyzer, loc, KilledKind::Revert)?;
                Ok(true)
            }
            1 => {
                // single edge
                self.result_func_ctx = self.genesis_func_ctx;
                let map = self.generate_replacement_map(analyzer, arena, inputs, func_mut)?;
                if let Some(res) = self.apply_replacement_map(analyzer, arena, &map, func_mut)? {
                    self.target_ctx.push_expr(res, analyzer)?;
                } else {
                    // unsat
                    self.target_ctx.kill(analyzer, loc, KilledKind::Revert)?;
                }
                Ok(true)
            }
            _ => {
                // multi-edge
                let new_forks = self
                    .target_ctx
                    .set_apply_forks(loc, edges.clone(), analyzer)
                    .unwrap();
                let map = self.generate_replacement_map(analyzer, arena, inputs, func_mut)?;
                edges.into_iter().zip(new_forks.into_iter()).try_for_each(
                    |(edge_ctx, new_target)| {
                        self.target_ctx = new_target;
                        self.result_func_ctx = edge_ctx;
                        if let Some(res) =
                            self.apply_replacement_map(analyzer, arena, &map, func_mut)?
                        {
                            self.target_ctx.push_expr(res, analyzer)?;
                        } else {
                            // unsat
                            self.target_ctx
                                .kill(analyzer, loc, KilledKind::Unreachable)?;
                        }
                        Ok(())
                    },
                )?;
                Ok(true)
            }
        }
    }
}

/// A trait for calling a function
pub trait FuncApplier:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ApplyStatTracker
{
    /// Applies a function to a given context with the provided inputs.
    ///
    /// This method is the entry point for function application. It sets up the necessary
    /// contexts and delegates the actual application process to the `ApplyContexts` struct.
    ///
    /// # Arguments
    ///
    /// * `arena` - A mutable reference to the `RangeArena` for element storage.
    /// * `ctx` - The target `ContextNode` where the function will be applied.
    /// * `func` - The `FunctionNode` representing the function to be applied.
    /// * `func_inputs` - A slice of `ContextVarNode` representing the function inputs.
    /// * `loc` - The `Loc` (location) information for error reporting.
    ///
    /// # Returns
    ///
    /// A `Result` containing a boolean indicating whether the application was successful (true)
    /// or not (false), or an `ExprErr` if an error occurred during the process.
    #[tracing::instrument(level = "trace", skip_all)]
    fn apply(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func: FunctionNode,
        func_inputs: &[ContextVarNode],
        loc: Loc,
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

            // if we have handled a function, we should have a body context already
            if self.handled_funcs().contains(&func) {
                return Ok(false);
            }

            self.handled_funcs_mut().push(func);
            if func.underlying(self).unwrap().body.is_some() {
                self.interpret_entry_func(func, arena);
            }

            if let Some(body_ctx) = func.maybe_body_ctx(self) {
                ctxs.genesis_func_ctx = body_ctx;
            } else {
                return Ok(false);
            }
        }

        ctxs.apply(self, arena, func_inputs, loc).into_expr_err(loc)
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
