use crate::helper::CallerHelper;
use crate::member_access::ListAccess;
use crate::variable::Variable;
use crate::Flatten;
use graph::elem::RangeArenaLike;
use graph::nodes::CallFork;
use graph::{AsDotStr, RangeEval};

use graph::{
    elem::{Elem, RangeElem, RangeExpr, RangeOp},
    nodes::{
        Concrete, ContextNode, ContextVarNode, ContractNode, ExprRet, FuncVis, FunctionNode,
        FunctionParamNode, KilledKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Range, SolcRange, VarType,
};
use shared::{
    AnalyzerLike, ExprErr, GraphError, IntoExprErr, NodeIdx, RangeArena, StorageLocation,
};

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
        self.recursive_storage_inputs(analyzer, self.target_ctx, &mut accumulated_vars)?;
        Ok(accumulated_vars)
    }

    /// Walk up the context tree accumulating all accessed storage variables
    pub fn recursive_storage_inputs(
        &self,
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
            self.recursive_storage_inputs(analyzer, parent, accumulated_vars)?;
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
        self.recursive_storage_params(analyzer, self.genesis_func_ctx, &mut accumulated_vars)?;
        Ok(accumulated_vars)
    }

    fn recursive_storage_params(
        &self,
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
                    self.recursive_storage_params(analyzer, c, accumulated_vars)?;
                }
                CallFork::Fork(w1, w2) => {
                    self.recursive_storage_params(analyzer, w1, accumulated_vars)?;
                    self.recursive_storage_params(analyzer, w2, accumulated_vars)?;
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
                let elem = Elem::from(input);
                mapping.insert(params[0].0.into(), (elem, input));
            } else {
                let mut param_iter = params.iter();
                let elem = Elem::from(input);
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
                    let elem = Elem::from(input_field);
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
                // if let Some(mut range) = new_var.ty.take_range() {
                //     // println!(
                //     //     "pre-ret range: [{}, {}]",
                //     //     range
                //     //         .min
                //     //         .recurse_dearenaize(analyzer, arena)
                //     //         .simplify_minimize(analyzer, arena)
                //     //         .unwrap(),
                //     //     range
                //     //         .max
                //     //         .recurse_dearenaize(analyzer, arena)
                //     //         .simplify_maximize(analyzer, arena)
                //     //         .unwrap()
                //     // );
                //     range.min = range.min.simplify_minimize(analyzer, arena).unwrap();
                //     range.max = range.max.simplify_maximize(analyzer, arena).unwrap();
                //     // println!("post-ret range: [{}, {}]", range.min, range.max);
                //     new_var.ty.set_range(range);
                // }
                let new_cvar = ContextVarNode::from(analyzer.add_node(new_var));
                analyzer.add_edge(
                    new_cvar,
                    self.target_ctx,
                    Edge::Context(ContextEdge::Variable),
                );
                self.target_ctx.add_var(new_cvar, analyzer).unwrap();
                if let Ok(fields) = ret.var().fielded_to_fields(analyzer) {
                    if fields.len() > 0 {
                        // println!("had field");
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
        // if let Some(idx) = arena.idx(&Elem::from(var)) {
        //     println!(
        //         "{}",
        //         arena.ranges[idx]
        //             .clone()
        //             .simplify_minimize(analyzer, arena)
        //             .unwrap()
        //     );
        // }
        if let Some(mut range) = var.ty_mut(analyzer)?.take_range() {
            println!(
                "pre range {}: [{}, {}], [{:#?}, {:#?}]",
                var.name(analyzer).unwrap(),
                range.min,
                range.max,
                range.min.recurse_dearenaize(analyzer, arena),
                range.max.recurse_dearenaize(analyzer, arena),
            );
            let mut range: SolcRange = range.take_flattened_range(analyzer, arena).unwrap().into();
            println!(
                "flattened range {}: [{}, {}], [{:#?}, {:#?}]",
                var.name(analyzer).unwrap(),
                range.min,
                range.max,
                range.min.recurse_dearenaize(analyzer, arena),
                range.max.recurse_dearenaize(analyzer, arena),
            );
            // use the replacement map
            replacement_map
                .iter()
                .try_for_each(|(replace, replacement)| {
                    println!("replace: {replace:?}, replacement: {}", replacement.0);
                    range.replace_dep(*replace, replacement.0.clone(), analyzer, arena)
                })?;

            println!(
                "post range {}: [{}, {}], [{:#?}, {:#?}]",
                var.name(analyzer).unwrap(),
                range.min,
                range.max,
                range.min.recurse_dearenaize(analyzer, arena),
                range.max.recurse_dearenaize(analyzer, arena),
            );
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
                let mut new_var = dep.underlying(analyzer)?.clone();
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
            // println!(
            //     "replacement map: {:#?}",
            //     map.iter()
            //         .map(|(k, (_, v))| {
            //             (
            //                 ExprRet::Single(*k).debug_str_ranged(analyzer, arena),
            //                 ExprRet::from(*v).debug_str_ranged(analyzer, arena),
            //             )
            //         })
            //         .collect::<Vec<_>>()
            // );
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
            ctxs.genesis_func_ctx = func.body_ctx(self);
        }

        ctxs.apply(self, arena, func_inputs).into_expr_err(loc)
        // ensure no modifiers (for now)
        // if pure function:
        //      grab requirements for context
        //      grab return node's simplified range
        //      replace fundamentals with function inputs
        //      update ctx name in place
        //
        // match func.visibility(self).into_expr_err(loc)? {
        //     FuncVis::Pure => {
        //         // pure functions are guaranteed to not require the use of state, so
        //         // the only things we care about are function inputs and function outputs
        //         if let Some(apply_ctx) = func.maybe_body_ctx(self) {
        // if apply_ctx
        //     .underlying(self)
        //     .into_expr_err(loc)?
        //     .child
        //     .is_some()
        // {
        //     tracing::trace!("Applying function: {}", func.name(self).into_expr_err(loc)?);
        //     let edges = apply_ctx.successful_edges(self).into_expr_err(loc)?;
        //     match edges.len() {
        //         0 => {
        //             ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
        //         }
        //         1 => {
        //             if !self.apply_pure(
        //                 arena,
        //                 loc,
        //                 func,
        //                 params,
        //                 func_inputs,
        //                 apply_ctx,
        //                 edges[0],
        //                 ctx,
        //                 false,
        //             )? {
        //                 ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
        //             }
        //             return Ok(true);
        //         }
        //         2.. => {
        //             tracing::trace!(
        //                 "Branching pure apply function: {}",
        //                 func.name(self).into_expr_err(loc)?
        //             );
        //             // self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
        //             let new_forks = ctx.set_apply_forks(loc, edges.clone(), self).unwrap();
        //             edges
        //                 .into_iter()
        //                 .zip(new_forks.iter())
        //                 .try_for_each(|(edge, new_fork)| {
        //                     let res = self.apply_pure(
        //                         arena,
        //                         loc,
        //                         func,
        //                         params,
        //                         func_inputs,
        //                         apply_ctx,
        //                         edge,
        //                         *new_fork,
        //                         true,
        //                     )?;
        //                     if !res {
        //                         new_fork
        //                             .kill(self, loc, KilledKind::Unreachable)
        //                             .into_expr_err(loc)?;
        //                         Ok(())
        //                     } else {
        //                         Ok(())
        //                     }
        //                 })?;
        //             return Ok(true);
        //         }
        //     }
        // } else {
        //     tracing::trace!(
        //         "Childless pure apply: {}",
        //         func.name(self).into_expr_err(loc)?
        //     );
        //     let res = self.apply_pure(
        //         arena,
        //         loc,
        //         func,
        //         params,
        //         func_inputs,
        //         apply_ctx,
        //         apply_ctx,
        //         ctx,
        //         false,
        //     )?;
        //     if !res {
        //         ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)?;
        //     }
        //     return Ok(true);
        // }
        //         } else {
        //             tracing::trace!("Pure function not processed");
        //             if ctx.associated_fn(self) == Ok(func) {
        //                 return Ok(false);
        //             }

        //             if seen.contains(&func) {
        //                 return Ok(false);
        //             }

        //             self.handled_funcs_mut().push(func);
        //             if func.underlying(self).unwrap().body.is_some() {
        //                 self.interpret_entry_func(func, arena);
        //             }

        //             seen.push(func);
        //             return self.apply(arena, ctx, loc, func, params, func_inputs, seen);
        //         }
        //     }
        //     FuncVis::View => {
        //         if let Some(body_ctx) = func.maybe_body_ctx(self) {
        //             if body_ctx
        //                 .underlying(self)
        //                 .into_expr_err(loc)?
        //                 .child
        //                 .is_some()
        //             {
        //                 let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
        //                 if edges.len() == 1 {
        //                     tracing::trace!(
        //                         "View apply function: {}",
        //                         func.name(self).into_expr_err(loc)?
        //                     );
        //                     self.add_completed_view(false, false, false, body_ctx);
        //                 } else {
        //                     tracing::trace!(
        //                         "Branching view apply function: {}",
        //                         func.name(self).into_expr_err(loc)?
        //                     );
        //                     self.add_completed_view(false, false, true, body_ctx);
        //                 }
        //             } else {
        //                 tracing::trace!(
        //                     "Childless view apply function: {}",
        //                     func.name(self).into_expr_err(loc)?
        //                 );
        //                 self.add_completed_view(false, true, false, body_ctx);
        //             }
        //         } else {
        //             tracing::trace!("View function not processed");
        //             if ctx.associated_fn(self) == Ok(func) {
        //                 return Ok(false);
        //             }

        //             if seen.contains(&func) {
        //                 return Ok(false);
        //             }

        //             self.handled_funcs_mut().push(func);
        //             if func.underlying(self).unwrap().body.is_some() {
        //                 self.interpret_entry_func(func, arena);
        //             }

        //             seen.push(func);
        //         }
        //     }
        //     FuncVis::Mut => {
        //         if let Some(body_ctx) = func.maybe_body_ctx(self) {
        //             if body_ctx
        //                 .underlying(self)
        //                 .into_expr_err(loc)?
        //                 .child
        //                 .is_some()
        //             {
        //                 let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
        //                 if edges.len() == 1 {
        //                     tracing::trace!(
        //                         "Mut apply function: {}",
        //                         func.name(self).into_expr_err(loc)?
        //                     );
        //                     self.add_completed_mut(false, false, false, body_ctx);
        //                 } else {
        //                     tracing::trace!(
        //                         "Branching mut apply function: {}",
        //                         func.name(self).into_expr_err(loc)?
        //                     );
        //                     self.add_completed_mut(false, false, true, body_ctx);
        //                 }
        //             } else {
        //                 tracing::trace!(
        //                     "Childless mut apply function: {}",
        //                     func.name(self).into_expr_err(loc)?
        //                 );
        //                 self.add_completed_mut(false, true, false, body_ctx);
        //             }
        //         } else {
        //             tracing::trace!("Mut function not processed");
        //             if ctx.associated_fn(self) == Ok(func) {
        //                 return Ok(false);
        //             }

        //             if seen.contains(&func) {
        //                 return Ok(false);
        //             }

        //             self.handled_funcs_mut().push(func);
        //             if func.underlying(self).unwrap().body.is_some() {
        //                 self.interpret_entry_func(func, arena);
        //             }

        //             seen.push(func);
        //         }
        //     }
        // }

        // Ok(false)
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
        todo!()
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
        // let mut replacement_map = Default::default();
        // self.basic_inputs(
        //     arena,
        //     apply_ctx,
        //     target_ctx,
        //     loc,
        //     params,
        //     func_inputs,
        //     replacement_map,
        // )?;
        // tracing::trace!("applying pure function - replacement map: {replacement_map:#?}");

        // let mut rets = self.update_returns()?;

        // if self.add_deps()? {
        //     // unsat
        //     return Ok(false);
        // }

        // let new_path = format!(
        //     "{}.{}.resume{{ {} }}",
        //     target_ctx.path(self),
        //     resulting_edge.path(self),
        //     target_ctx.associated_fn_name(self).unwrap()
        // );
        // let underlying_mut = target_ctx.underlying_mut(self).into_expr_err(loc)?;
        // underlying_mut.path = new_path;

        // target_ctx
        //     .propogate_applied(func, self)
        //     .into_expr_err(loc)?;
        // if let Some(body) = func.maybe_body_ctx(self) {
        //     for app in body.underlying(self).into_expr_err(loc)?.applies.clone() {
        //         target_ctx.propogate_applied(app, self).into_expr_err(loc)?;
        //     }
        // }

        // target_ctx
        //     .push_expr(ExprRet::Multi(rets), self)
        //     .into_expr_err(loc)?;
        // self.add_completed_pure(true, false, forks, resulting_edge);
        // Ok(true)
    }

    fn update_returns(&mut self) -> Result<Vec<ContextVarNode>, ExprErr> {
        todo!()
        // resulting_edge
        //     .return_nodes(self)
        //     .into_expr_err(loc)?
        //     .iter()
        //     .enumerate()
        //     .map(|(i, ret)| {
        //         let mut new_var = ret.var().underlying(self).unwrap().clone();
        //         let new_name = format!(
        //             "tmp_{}({}.{i})",
        //             target_ctx.new_tmp(self).unwrap(),
        //             func.loc_specified_name(self).unwrap()
        //         );
        //         tracing::trace!("handling apply return: {new_name}");
        //         new_var.name.clone_from(&new_name);
        //         new_var.display_name = new_name.clone();
        //         if let Some(mut range) = new_var.ty.take_range() {
        //             let mut range: SolcRange =
        //                 range.take_flattened_range(self, arena).unwrap().into();
        //             tracing::trace!(
        //                 "apply return {new_name} target range: [{}, {}]",
        //                 range.range_min(),
        //                 // .to_range_string(false, self, arena)
        //                 // .s,
        //                 range.range_max() // .to_range_string(false, self, arena)
        //                                   // .s,
        //             );
        //             replacement_map.iter().for_each(|(replace, replacement)| {
        //                 range.replace_dep(*replace, replacement.0.clone(), self, arena);
        //             });

        //             range.cache_eval(self, arena).unwrap();

        //             tracing::trace!(
        //                 "apply return {new_name} range: {}",
        //                 range.as_dot_str(self, arena)
        //             );
        //             // TODO: change ty here to match ret type
        //             new_var.ty.set_range(range).unwrap();
        //         }

        //         if let Some(ref mut dep_on) = &mut new_var.dep_on {
        //             dep_on.iter_mut().for_each(|d| {
        //                 if let Some((_, r)) = replacement_map.get(&(*d).into()) {
        //                     *d = *r
        //                 }
        //             });
        //         }

        //         let mut new_cvar = ContextVarNode::from(self.add_node(new_var));
        //         self.add_edge(new_cvar, target_ctx, Edge::Context(ContextEdge::Variable));
        //         target_ctx.add_var(new_cvar, self).unwrap();

        //         // handle the case where the return node is a struct
        //         if let Ok(fields) = ret.var().fielded_to_fields(self) {
        //             if !fields.is_empty() {
        //                 fields.iter().for_each(|field| {
        //                     let mut new_var = field.underlying(self).unwrap().clone();
        //                     let new_name = format!(
        //                         "{}.{i}.{}",
        //                         func.loc_specified_name(self).unwrap(),
        //                         field.name(self).unwrap()
        //                     );
        //                     new_var.name.clone_from(&new_name);
        //                     new_var.display_name = new_name;
        //                     if let Some(mut range) = new_var.ty.take_range() {
        //                         let mut range: SolcRange =
        //                             range.take_flattened_range(self, arena).unwrap().into();
        //                         replacement_map.iter().for_each(|(replace, replacement)| {
        //                             range.replace_dep(*replace, replacement.0.clone(), self, arena);
        //                         });

        //                         range.cache_eval(self, arena).unwrap();

        //                         new_var.ty.set_range(range).unwrap();
        //                     }

        //                     if let Some(ref mut dep_on) = &mut new_var.dep_on {
        //                         dep_on.iter_mut().for_each(|d| {
        //                             if let Some((_, r)) = replacement_map.get(&(*d).into()) {
        //                                 *d = *r
        //                             }
        //                         });
        //                     }
        //                     let new_field = ContextVarNode::from(self.add_node(new_var));
        //                     self.add_edge(
        //                         new_field,
        //                         new_cvar,
        //                         Edge::Context(ContextEdge::AttrAccess("field")),
        //                     );
        //                 });
        //             }
        //         } else {
        //             let next_cvar = self
        //                 .advance_var_in_ctx_forcible(arena, new_cvar, loc, target_ctx, true)
        //                 .unwrap();
        //             let casted = Elem::Expr(RangeExpr::new(
        //                 Elem::from(new_cvar),
        //                 RangeOp::Cast,
        //                 Elem::from(ret.var()),
        //             ));
        //             next_cvar
        //                 .set_range_min(self, arena, casted.clone())
        //                 .unwrap();
        //             next_cvar.set_range_max(self, arena, casted).unwrap();

        //             new_cvar = next_cvar;
        //         }

        //         ExprRet::Single(new_cvar.latest_version(self).into())
        //     })
        //     .collect()
    }

    fn add_deps(&mut self) -> Result<bool, ExprErr> {
        todo!()
        // let mut unsat = false;
        // resulting_edge
        //     .ctx_deps(self)
        //     .into_expr_err(loc)?
        //     .iter()
        //     .try_for_each(|dep| {
        //         let mut new_var = dep.underlying(self)?.clone();
        //         if let Some(mut range) = new_var.ty.take_range() {
        //             // let mut range: SolcRange =
        //             // range.take_flattened_range(self).unwrap().into();
        //             let mut range: SolcRange =
        //                 range.flattened_range(self, arena)?.into_owned().into();
        //             replacement_map.iter().for_each(|(replace, replacement)| {
        //                 range.replace_dep(*replace, replacement.0.clone(), self, arena);
        //             });

        //             range.cache_eval(self, arena)?;
        //             new_var.ty.set_range(range)?;
        //         }

        //         if let Some(ref mut dep_on) = &mut new_var.dep_on {
        //             dep_on.iter_mut().for_each(|d| {
        //                 if let Some((_, r)) = replacement_map.get(&(*d).into()) {
        //                     *d = *r
        //                 }
        //             });
        //         }
        //         let new_cvar = ContextVarNode::from(self.add_node(new_var));

        //         if new_cvar.is_const(self, arena)?
        //             && new_cvar.evaled_range_min(self, arena)?
        //                 == Some(Elem::from(Concrete::from(false)))
        //         {
        //             unsat = true;
        //         }
        //         self.add_edge(new_cvar, target_ctx, Edge::Context(ContextEdge::Variable));
        //         target_ctx.add_var(new_cvar, self)?;
        //         target_ctx.add_ctx_dep(new_cvar, self, arena)
        //     })
        //     .into_expr_err(loc)?;

        // Ok(unsat)
    }

    fn inputs_replacement_map(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        apply_ctx: ContextNode,
        target_ctx: ContextNode,
        params: &[FunctionParamNode],
        inputs: ApplyInputs,
        loc: Loc,
    ) -> Result<BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>, ExprErr> {
        todo!()
        // let inputs = apply_ctx.input_variables(self);
        // let mut replacement_map: BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)> =
        //     BTreeMap::default();
        // // Map inputs to params
        // self.basic_inputs(
        //     arena,
        //     apply_ctx,
        //     target_ctx,
        //     params,
        //     inputs.func_inputs,
        //     &mut replacement_map,
        //     loc,
        // );

        // // Map storage to storage
        // if let Some(storage_inputs) = inputs.storage_inputs {}
        // Ok(replacement_map)
    }

    fn basic_inputs(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        apply_ctx: ContextNode,
        target_ctx: ContextNode,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
        replacement_map: &mut BTreeMap<NodeIdx, (Elem<Concrete>, ContextVarNode)>,
        loc: Loc,
    ) {
        todo!()
        // params.iter().try_for_each(|param| {
        //     if let Some(name) = param.maybe_name(self).into_expr_err(loc)? {
        //         let input_loc = param.loc(self).into_expr_err(loc)?;
        //         let input_storage = param.underlying(self).unwrap().storage;
        //         let replacement = self.create_replacement_var(
        //             target_ctx,
        //             func_inputs,
        //             &name,
        //             input_storage,
        //             input_loc,
        //         )?;

        //         // Cast the input variable if needed
        //         if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self).unwrap()) {
        //             replacement
        //                 .cast_from_ty(param_ty, self, arena)
        //                 .into_expr_err(loc)?;
        //         }

        //         // TODO: this is wrong
        //         // if let Some(_len_var) = replacement.array_to_len_var(self) {
        //         //     // bring the length variable along as well
        //         //     let _ = self.get_length(arena, apply_ctx, *func_input, true, loc)
        //         //         .unwrap();
        //         // }

        //         let target_fields = correct_input.fielded_to_fields(self).into_expr_err(loc)?;
        //         let replacement_fields = func_input.fielded_to_fields(self).into_expr_err(loc)?;
        //         let match_field = |this: &Self,
        //                            target_field: ContextVarNode,
        //                            replacement_fields: &[ContextVarNode]|
        //          -> Option<(ContextVarNode, ContextVarNode)> {
        //             let target_full_name = target_field.name(this).clone().unwrap();
        //             let target_field_name = target_full_name
        //                 .split('.')
        //                 .collect::<Vec<_>>()
        //                 .last()
        //                 .cloned()
        //                 .unwrap();
        //             let replacement_field = replacement_fields.iter().find(|rep_field| {
        //                 let replacement_full_name = rep_field.name(this).unwrap();
        //                 let replacement_field_name = replacement_full_name
        //                     .split('.')
        //                     .collect::<Vec<_>>()
        //                     .last()
        //                     .cloned()
        //                     .unwrap();
        //                 replacement_field_name == target_field_name
        //             })?;
        //             Some((target_field, *replacement_field))
        //         };

        //         let mut struct_stack = target_fields
        //             .into_iter()
        //             .filter_map(|i| match_field(self, i, &replacement_fields[..]))
        //             .collect::<Vec<_>>();

        //         while let Some((target_field, replacement_field)) = struct_stack.pop() {
        //             let mut replacement_field_as_elem = Elem::from(replacement_field);
        //             replacement_field_as_elem.arenaize(self, arena).unwrap();
        //             let to_replace = target_field.next_version(self).unwrap_or(target_field);
        //             replacement_map.insert(
        //                 to_replace.0.into(),
        //                 (replacement_field_as_elem.clone(), replacement_field),
        //             );

        //             let target_sub_fields =
        //                 target_field.fielded_to_fields(self).into_expr_err(loc)?;
        //             let replacement_sub_fields = replacement_field
        //                 .fielded_to_fields(self)
        //                 .into_expr_err(loc)?;
        //             let subs = target_sub_fields
        //                 .into_iter()
        //                 .filter_map(|i| match_field(self, i, &replacement_sub_fields[..]))
        //                 .collect::<Vec<_>>();
        //             struct_stack.extend(subs);
        //         }

        //         let mut replacement_as_elem = Elem::from(replacement);
        //         replacement_as_elem
        //             .arenaize(self, arena)
        //             .into_expr_err(loc)?;

        //         replacement_map.insert(correct_input.0.into(), (replacement_as_elem, replacement));
        //     }
        //     Ok(())
        // })?;
    }

    fn create_replacement_var(
        &mut self,
        target_ctx: ContextNode,
        inputs: &[ContextVarNode],
        input_name: &String,
        input_storage: Option<StorageLocation>,
        input_loc: Loc,
    ) -> Result<ContextVarNode, ExprErr> {
        todo!()
        // // find the correct input from the inputs
        // let Some(correct_input) = inputs
        //     .iter()
        //     .find(|input| input.name(self).unwrap() == input_name)
        // else {
        //     return Err(ExprErr::InvalidFunctionInput(
        //         loc,
        //         "Could not match input to parameter".to_string(),
        //     ));
        // };

        // // construct the input variable
        // let mut new_cvar = correct_input
        //     .latest_version_or_inherited_in_ctx(apply_ctx, self)
        //     .underlying(self)
        //     .into_expr_err(loc)?
        //     .clone();
        // new_cvar.loc = Some(input_loc);
        // new_cvar.is_tmp = false;
        // new_cvar.storage = input_storage;

        // let replacement = ContextVarNode::from(self.add_node(new_cvar));

        // self.add_edge(
        //     replacement,
        //     target_ctx,
        //     Edge::Context(ContextEdge::Variable),
        // );
        // target_ctx.add_var(replacement, self).unwrap();

        // Ok(replacement)
    }

    // fn handle_struct_replacement(&mut self, replacement_fields: Vec<ContextVarNode>, )
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
