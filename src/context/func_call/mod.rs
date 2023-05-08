use crate::context::exprs::IntoExprErr;
use crate::context::func_call::{
    internal_call::InternalFuncCaller, intrinsic_call::IntrinsicFuncCaller,
    namespaced_call::NameSpaceFuncCaller,
};
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use itertools::Itertools;
use shared::analyzer::AsDotStr;

use shared::analyzer::GraphLike;
use shared::context::ExprRet;
use shared::context::*;
use solang_parser::helpers::CodeLocation;
use std::collections::BTreeMap;

use shared::range::Range;
use solang_parser::pt::{Expression, Loc, NamedArgument, StorageLocation};

use crate::VarType;

use shared::{analyzer::AnalyzerLike, nodes::*, Edge, Node, NodeIdx};

pub mod internal_call;
pub mod intrinsic_call;
pub mod modifier;
pub mod namespaced_call;

impl<T> FuncCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
}
pub trait FuncCaller:
    GraphLike + AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized
{
    #[tracing::instrument(level = "trace", skip_all)]
    fn named_fn_call_expr(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        func_expr: &Expression,
        input_exprs: &[NamedArgument],
    ) -> Result<(), ExprErr> {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => {
                self.call_name_spaced_named_func(ctx, loc, member_expr, ident, input_exprs)
            }
            Variable(ident) => self.call_internal_named_func(ctx, loc, ident, input_exprs),
            e => Err(ExprErr::IntrinsicNamedArgs(
                *loc,
                format!("Cannot call intrinsic functions with named arguments. Call: {e:?}"),
            )),
        }
    }
    #[tracing::instrument(level = "trace", skip_all)]
    fn fn_call_expr(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        func_expr: &Expression,
        input_exprs: &[Expression],
    ) -> Result<(), ExprErr> {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => {
                self.call_name_spaced_func(ctx, loc, member_expr, ident, input_exprs)
            }
            Variable(ident) => self.call_internal_func(ctx, loc, ident, func_expr, input_exprs),
            _ => {
                self.parse_ctx_expr(func_expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Function call to nonexistent function".to_string()))
                    };

                    analyzer.match_intrinsic_fallback(ctx, &loc, input_exprs, ret)
                })
            }
        }
    }

    fn match_intrinsic_fallback(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        input_exprs: &[Expression],
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(func_idx) | ExprRet::SingleLiteral(func_idx) => {
                self.intrinsic_func_call(loc, input_exprs, func_idx, ctx)
            }
            ExprRet::Multi(inner) => inner
                .into_iter()
                .try_for_each(|ret| self.match_intrinsic_fallback(ctx, loc, input_exprs, ret)),
            ExprRet::CtxKilled => {
                ctx.push_expr(ExprRet::CtxKilled, self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
        }
    }

    /// Disambiguates a function call by their inputs (length & type)
    fn disambiguate_fn_call(
        &mut self,
        fn_name: &str,
        literals: Vec<bool>,
        input_paths: &ExprRet,
        funcs: &[FunctionNode],
    ) -> Option<FunctionNode> {
        let input_paths = input_paths.clone().flatten();
        // try to find the function based on naive signature
        // This doesnt do type inference on NumberLiterals (i.e. 100 could be uintX or intX, and there could
        // be a function that takes an int256 but we evaled as uint256)
        let fn_sig = format!("{}{}", fn_name, input_paths.try_as_func_input_str(self));
        if let Some(func) = funcs.iter().find(|func| func.name(self).unwrap() == fn_sig) {
            return Some(*func);
        }

        // filter by input len
        let inputs = input_paths.as_flat_vec();
        let funcs: Vec<&FunctionNode> = funcs
            .iter()
            .filter(|func| func.params(self).len() == inputs.len())
            .collect();

        if funcs.len() == 1 {
            return Some(*funcs[0]);
        }

        if !literals.iter().any(|i| *i) {
            None
        } else {
            let funcs = funcs
                .iter()
                .filter(|func| {
                    let params = func.params(self);
                    params
                        .iter()
                        .zip(&inputs)
                        .enumerate()
                        .all(|(i, (param, input))| {
                            if param.as_dot_str(self)
                                == ContextVarNode::from(*input).as_dot_str(self)
                            {
                                true
                            } else if literals[i] {
                                let as_concrete =
                                    ContextVarNode::from(*input).as_concrete(self).unwrap();
                                let possibilities = as_concrete.possible_builtins_from_ty_inf();
                                let param_ty = param.ty(self).unwrap();
                                match self.node(param_ty) {
                                    Node::Builtin(b) => possibilities.contains(b),
                                    _ => false,
                                }
                            } else {
                                false
                            }
                        })
                })
                .collect::<Vec<_>>();
            if funcs.len() == 1 {
                Some(**funcs[0])
            } else {
                // this would be invalid solidity, likely the user needs to perform a cast
                None
            }
        }
    }

    fn parse_inputs(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        inputs: &[Expression],
    ) -> Result<(), ExprErr> {
        inputs
            .iter()
            .try_for_each(|input| {
                println!("input: {input:#?}");
                self.parse_ctx_expr(input, ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Inputs did not have left hand sides".to_string()));
                    };
                    ctx.push_lhs_expr(ret, analyzer).into_expr_err(loc)
                })
            })?;
        if !inputs.is_empty() {
            self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_lhs_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(loc, "Inputs did not have left hand sides".to_string()));
                };
                ctx.push_expr(ret, analyzer).into_expr_err(loc)
            })
        } else {
            Ok(())
        }
    }

    /// Setups up storage variables for a function call and calls it
    fn setup_fn_call(
        &mut self,
        loc: &Loc,
        inputs: &ExprRet,
        func_idx: NodeIdx,
        ctx: ContextNode,
        func_call_str: Option<&str>,
    ) -> Result<(), ExprErr> {
        // if we have a single match thats our function
        let var = match ContextVar::maybe_from_user_ty(self, *loc, func_idx) {
            Some(v) => v,
            None => panic!(
                "Could not create context variable from user type: {:?}",
                self.node(func_idx)
            ),
        };

        let new_cvarnode = self.add_node(Node::ContextVar(var));
        self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
        if let Some(func_node) = ContextVarNode::from(new_cvarnode)
            .ty(self)
            .into_expr_err(*loc)?
            .func_node(self)
        {
            self.func_call(ctx, *loc, inputs, func_node, func_call_str, None)
        } else {
            unreachable!()
        }
    }

    /// Matches the input kinds and performs the call
    fn func_call(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        input_paths: &ExprRet,
        func: FunctionNode,
        func_call_str: Option<&str>,
        modifier_state: Option<ModifierState>,
    ) -> Result<(), ExprErr> {
        let params = func.params(self);
        let input_paths = input_paths.clone().flatten();
        if input_paths.has_killed() {
            ctx.push_expr(ExprRet::CtxKilled, self).into_expr_err(loc)?;
            return Ok(());
        }
        match input_paths {
            ExprRet::Single(input_var) | ExprRet::SingleLiteral(input_var) => {
                // if we get a single var, we expect the func to only take a single
                // variable
                self.func_call_inner(
                    false,
                    ctx,
                    func,
                    loc,
                    vec![ContextVarNode::from(input_var).latest_version(self)],
                    params,
                    func_call_str,
                    modifier_state,
                )
            }
            ExprRet::Multi(ref inputs) => {
                if ExprRet::Multi(inputs.to_vec()).flatten().has_killed() {
                    ctx.push_expr(ExprRet::CtxKilled, self).into_expr_err(loc)?;
                    return Ok(());
                }
                // check if the inputs length matchs func params length
                // if they do, check that none are forks
                if inputs.len() == params.len() {
                    let input_vars = inputs
                        .iter()
                        .map(|expr_ret| {
                            let var = expr_ret.expect_single().into_expr_err(loc)?;
                            Ok(ContextVarNode::from(var).latest_version(self))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    self.func_call_inner(
                        false,
                        ctx,
                        func,
                        loc,
                        input_vars,
                        params,
                        func_call_str,
                        modifier_state,
                    )
                } else {
                    Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "Length mismatch: {inputs:?} {params:?}, inputs as vars: {}, ctx: {}",
                            ExprRet::Multi(inputs.to_vec()).debug_str(self),
                            ctx.path(self)
                        ),
                    ))
                }
            }
            e => todo!("here: {:?}", e),
        }
    }

    fn create_call_ctx(
        &mut self,
        curr_ctx: ContextNode,
        loc: Loc,
        func_node: FunctionNode,
        modifier_state: Option<ModifierState>,
    ) -> Result<ContextNode, ExprErr> {
        let fn_ext = curr_ctx.is_fn_ext(func_node, self).into_expr_err(loc)?;
        let callee_ctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(
                    curr_ctx,
                    None,
                    loc,
                    None,
                    Some(func_node),
                    fn_ext,
                    self,
                    modifier_state,
                )
                .into_expr_err(loc)?,
            )),
        );
        curr_ctx
            .set_child_call(callee_ctx, self)
            .into_expr_err(loc)?;
        let ctx_fork = self.add_node(Node::FunctionCall);
        self.add_edge(ctx_fork, curr_ctx, Edge::Context(ContextEdge::Subcontext));
        self.add_edge(ctx_fork, func_node, Edge::Context(ContextEdge::Call));
        self.add_edge(
            NodeIdx::from(callee_ctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        Ok(callee_ctx)
    }

    /// Maps inputs to function parameters such that if there is a renaming i.e. `a(uint256 x)` is called via `a(y)`,
    /// we map `y -> x` for future lookups
    fn map_inputs_to_params(
        &mut self,
        loc: Loc,
        entry_call: bool,
        params: Vec<FunctionParamNode>,
        inputs: Vec<ContextVarNode>,
        callee_ctx: ContextNode,
    ) -> Result<BTreeMap<ContextVarNode, ContextVarNode>, ExprErr> {
        Ok(params
            .iter()
            .zip(inputs.iter())
            .filter_map(|(param, input)| {
                if !entry_call {
                    if let Some(name) =
                        self.add_if_err(param.maybe_name(self).into_expr_err(loc))?
                    {
                        let res = input
                            .latest_version(self)
                            .underlying(self)
                            .into_expr_err(loc)
                            .cloned();
                        let mut new_cvar = self.add_if_err(res)?;
                        new_cvar.loc = Some(param.loc(self).unwrap());
                        new_cvar.name = name.clone();
                        new_cvar.display_name = name;
                        new_cvar.is_tmp = false;
                        new_cvar.storage = if let Some(StorageLocation::Storage(_)) =
                            param.underlying(self).unwrap().storage
                        {
                            new_cvar.storage
                        } else {
                            None
                        };

                        if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self).unwrap())
                        {
                            let ty = new_cvar.ty.clone();
                            if !ty.ty_eq(&param_ty, self).unwrap() {
                                if let Some(new_ty) = ty.try_cast(&param_ty, self).unwrap() {
                                    new_cvar.ty = new_ty;
                                }
                            }
                        }

                        let node = ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));
                        self.add_edge(
                            node,
                            input.latest_version(self),
                            Edge::Context(ContextEdge::InputVariable),
                        );

                        if let (Some(r), Some(r2)) =
                            (node.range(self).unwrap(), param.range(self).unwrap())
                        {
                            let new_min = r.range_min().cast(r2.range_min());
                            let new_max = r.range_max().cast(r2.range_max());
                            let res = node.try_set_range_min(self, new_min).into_expr_err(loc);
                            self.add_if_err(res);
                            let res = node.try_set_range_max(self, new_max).into_expr_err(loc);
                            self.add_if_err(res);
                            let res = node
                                .try_set_range_exclusions(self, r.exclusions)
                                .into_expr_err(loc);
                            self.add_if_err(res);
                        }
                        self.add_edge(node, callee_ctx, Edge::Context(ContextEdge::Variable));
                        Some((*input, node))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, ContextVarNode>>())
    }

    /// Checks if there are any modifiers and executes them prior to executing the function
    #[tracing::instrument(level = "trace", skip_all)]
    fn func_call_inner(
        &mut self,
        entry_call: bool,
        ctx: ContextNode,
        func_node: FunctionNode,
        loc: Loc,
        inputs: Vec<ContextVarNode>,
        params: Vec<FunctionParamNode>,
        func_call_str: Option<&str>,
        modifier_state: Option<ModifierState>,
    ) -> Result<(), ExprErr> {
        // pseudocode:
        //  1. Create context for the call
        //  2. Check for modifiers
        //  3. Call modifier 0, then 1, then 2, etc.
        //  4. Call this function
        //  5. Finish modifier 2, then 1, then 0

        let callee_ctx = if entry_call {
            ctx
        } else {
            self.create_call_ctx(ctx, loc, func_node, modifier_state)?
        };

        // handle remapping of variable names and bringing variables into the new context
        let renamed_inputs =
            self.map_inputs_to_params(loc, entry_call, params, inputs, callee_ctx)?;

        // begin modifier handling by making sure modifiers were set
        if !func_node.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(func_node, ctx)?;
        }

        // get modifiers
        let mods = func_node.modifiers(self);
        self.apply_to_edges(callee_ctx, loc, &|analyzer, callee_ctx, loc| {
            if let Some(mod_state) = &ctx.underlying(analyzer).into_expr_err(loc)?.modifier_state {
                // we are iterating through modifiers
                if mod_state.num + 1 < mods.len() {
                    // use the next modifier
                    let mut mstate = mod_state.clone();
                    mstate.num += 1;
                    analyzer.call_modifier_for_fn(loc, callee_ctx, func_node, mstate)
                } else {
                    // out of modifiers, execute the actual function call
                    analyzer.execute_call_inner(
                        loc,
                        ctx,
                        callee_ctx,
                        func_node,
                        &renamed_inputs,
                        func_call_str,
                    )
                }
            } else if !mods.is_empty() {
                // we have modifiers and havent executed them, start the process of executing them
                let state =
                    ModifierState::new(0, loc, func_node, callee_ctx, ctx, renamed_inputs.clone());
                analyzer.call_modifier_for_fn(loc, callee_ctx, func_node, state)
            } else {
                // no modifiers, just execute the function
                analyzer.execute_call_inner(
                    loc,
                    ctx,
                    callee_ctx,
                    func_node,
                    &renamed_inputs,
                    func_call_str,
                )
            }
        })
    }

    /// Actually executes the function
    #[tracing::instrument(level = "trace", skip_all)]
    fn execute_call_inner(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        func_node: FunctionNode,
        renamed_inputs: &BTreeMap<ContextVarNode, ContextVarNode>,
        func_call_str: Option<&str>,
    ) -> Result<(), ExprErr> {
        if let Some(body) = func_node.underlying(self).into_expr_err(loc)?.body.clone() {
            // add return nodes into the subctx
            func_node.returns(self).iter().for_each(|ret| {
                if let Some(var) =
                    ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).unwrap().clone())
                {
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, callee_ctx, Edge::Context(ContextEdge::Variable));
                }
            });

            self.parse_ctx_statement(&body, false, Some(callee_ctx));
            self.ctx_rets(loc, caller_ctx, callee_ctx)
        } else {
            self.inherit_input_changes(loc, caller_ctx, callee_ctx, renamed_inputs)?;
            self.inherit_storage_changes(loc, caller_ctx, callee_ctx)?;
            self.apply_to_edges(callee_ctx, loc, &|analyzer, ctx, loc| {
                func_node.returns(analyzer).iter().try_for_each(|ret| {
                    let underlying = ret.underlying(analyzer).unwrap();
                    let mut var = ContextVar::new_from_func_ret(ctx, analyzer, underlying.clone())
                        .unwrap()
                        .expect("No type for return variable?");
                    if let Some(func_call) = &func_call_str {
                        var.name =
                            format!("{}_{}", func_call, callee_ctx.new_tmp(analyzer).unwrap());
                        var.display_name = func_call.to_string();
                    }
                    let node = analyzer.add_node(Node::ContextVar(var));
                    analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Return));
                    ctx.push_expr(ExprRet::Single(node), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            })
        }
    }

    fn ctx_rets(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "Handling function call return for: {}, {}",
            caller_ctx.path(self),
            callee_ctx.path(self)
        );
        match callee_ctx.underlying(self).into_expr_err(loc)?.child {
            Some(CallFork::Fork(w1, w2)) => {
                self.ctx_rets(loc, caller_ctx, w1)?;
                self.ctx_rets(loc, caller_ctx, w2)
            }
            Some(CallFork::Call(c))
                if c.underlying(self).into_expr_err(loc)?.depth
                    >= caller_ctx.underlying(self).into_expr_err(loc)?.depth =>
            {
                // follow rabbit hole
                self.ctx_rets(loc, caller_ctx, c)
            }
            _ => {
                let callee_depth = callee_ctx.underlying(self).into_expr_err(loc)?.depth;
                let caller_depth = caller_ctx.underlying(self).into_expr_err(loc)?.depth;
                if callee_depth != caller_depth {
                    let ret_subctx = ContextNode::from(
                        self.add_node(Node::Context(
                            Context::new_subctx(
                                callee_ctx,
                                Some(caller_ctx),
                                loc,
                                None,
                                None,
                                false,
                                self,
                                caller_ctx
                                    .underlying(self)
                                    .into_expr_err(loc)?
                                    .modifier_state
                                    .clone(),
                            )
                            .unwrap(),
                        )),
                    );
                    self.add_edge(ret_subctx, caller_ctx, Edge::Context(ContextEdge::Continue));

                    // TODO: keep the stack here!!!
                    let res = callee_ctx
                        .set_child_call(ret_subctx, self)
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);

                    callee_ctx
                        .underlying(self)
                        .unwrap()
                        .ret
                        .clone()
                        .into_iter()
                        .enumerate()
                        .try_for_each(|(i, (_, node))| {
                            let tmp_ret = node
                                .as_tmp(callee_ctx.underlying(self).unwrap().loc, ret_subctx, self)
                                .unwrap();
                            tmp_ret.underlying_mut(self).unwrap().is_return = true;
                            tmp_ret.underlying_mut(self).unwrap().display_name =
                                format!("{}.{}", callee_ctx.associated_fn_name(self).unwrap(), i);
                            // println!("")
                            self.add_edge(
                                tmp_ret,
                                ret_subctx,
                                Edge::Context(ContextEdge::Variable),
                            );
                            ret_subctx
                                .push_expr(ExprRet::Single(tmp_ret.into()), self)
                                .into_expr_err(loc)?;
                            Ok(())
                        })
                } else {
                    callee_ctx
                        .underlying(self)
                        .unwrap()
                        .ret
                        .clone()
                        .into_iter()
                        .try_for_each(|(_, node)| {
                            callee_ctx
                                .push_expr(ExprRet::Single(node.into()), self)
                                .into_expr_err(loc)?;
                            Ok(())
                        })
                }
            }
        }
    }

    /// Calls a modifier for a function
    #[tracing::instrument(level = "trace", skip_all)]
    fn call_modifier_for_fn(
        &mut self,
        loc: Loc,
        func_ctx: ContextNode,
        func_node: FunctionNode,
        mod_state: ModifierState,
    ) -> Result<(), ExprErr> {
        let mod_node = func_node.modifiers(self)[mod_state.num];
        tracing::trace!(
            "calling modifier {} for func {}",
            mod_node.name(self).into_expr_err(loc)?,
            func_node.name(self).into_expr_err(loc)?
        );

        let input_exprs = func_node
            .modifier_input_vars(mod_state.num, self)
            .into_expr_err(loc)?;

        input_exprs
            .iter()
            .try_for_each(|expr| self.parse_ctx_expr(expr, func_ctx))?;
        self.apply_to_edges(func_ctx, loc, &|analyzer, ctx, loc| {
            let input_paths = if input_exprs.is_empty() {
                ExprRet::Multi(vec![])
            } else {
                let Some(input_paths) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoRhs(loc, format!("No inputs to modifier, expected: {}", input_exprs.len())))
                };
                input_paths
            };

            analyzer.func_call(
                ctx,
                loc,
                &input_paths,
                mod_node,
                None,
                Some(mod_state.clone()),
            )
        })
    }

    /// Resumes the parent function of a modifier
    #[tracing::instrument(level = "trace", skip_all)]
    fn resume_from_modifier(
        &mut self,
        ctx: ContextNode,
        modifier_state: ModifierState,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "resuming from modifier: {}",
            ctx.associated_fn_name(self)
                .into_expr_err(modifier_state.loc)?
        );

        let mods = modifier_state.parent_fn.modifiers(self);
        self.apply_to_edges(ctx, modifier_state.loc, &|analyzer, ctx, _loc| {
            if modifier_state.num + 1 < mods.len() {
                // use the next modifier
                let mut mstate = modifier_state.clone();
                mstate.num += 1;
                analyzer.call_modifier_for_fn(
                    mods[mstate.num]
                        .underlying(analyzer)
                        .into_expr_err(mstate.loc)?
                        .loc,
                    ctx,
                    mstate.parent_fn,
                    mstate,
                )?;
                Ok(())
            } else {
                let new_parent_subctx = ContextNode::from(
                    analyzer.add_node(Node::Context(
                        Context::new_subctx(
                            ctx,
                            Some(modifier_state.parent_ctx),
                            modifier_state.loc,
                            None,
                            None,
                            false,
                            analyzer,
                            None,
                        )
                        .unwrap(),
                    )),
                );

                analyzer.add_edge(
                    new_parent_subctx,
                    modifier_state.parent_ctx,
                    Edge::Context(ContextEdge::Continue),
                );
                ctx.set_child_call(new_parent_subctx, analyzer)
                    .into_expr_err(modifier_state.loc)?;

                // modifier_state.parent_ctx.vars(self).iter().try_for_each(|var| {
                //     self.advance_var_in_ctx(var.latest_version(self), modifier_state.loc, new_parent_subctx)?;
                //     Ok(())
                // })?;

                // pass up the variable changes
                // self.inherit_input_changes(
                //     modifier_state.loc,
                //     new_parent_subctx,
                //     ctx,
                //     &modifier_state.renamed_inputs,
                // )?;
                // self.inherit_storage_changes(new_parent_subctx, ctx)
                //     .into_expr_err(modifier_state.loc)?;

                // actually execute the parent function
                analyzer.execute_call_inner(
                    modifier_state.loc,
                    ctx,
                    new_parent_subctx,
                    modifier_state.parent_fn,
                    &modifier_state.renamed_inputs,
                    None,
                )?;

                let edges = new_parent_subctx
                    .live_edges(analyzer)
                    .into_expr_err(modifier_state.loc)?;

                fn inherit_return_from_call(
                    analyzer: &mut (impl GraphLike + AnalyzerLike),
                    loc: Loc,
                    ctx: ContextNode,
                ) -> Result<(), ExprErr> {
                    let modifier_after_subctx = ContextNode::from(
                        analyzer.add_node(Node::Context(
                            Context::new_subctx(
                                ctx,
                                Some(ctx),
                                loc,
                                None,
                                None,
                                false,
                                analyzer,
                                None,
                            )
                            .unwrap(),
                        )),
                    );

                    ctx.set_child_call(modifier_after_subctx, analyzer)
                        .into_expr_err(loc)?;
                    analyzer.add_edge(
                        modifier_after_subctx,
                        ctx,
                        Edge::Context(ContextEdge::Continue),
                    );

                    let ret = ctx.underlying(analyzer).unwrap().ret.clone();
                    modifier_after_subctx.underlying_mut(analyzer).unwrap().ret = ret;
                    Ok(())
                }

                if edges.is_empty() {
                    inherit_return_from_call(analyzer, modifier_state.loc, new_parent_subctx)?;
                } else {
                    edges.iter().try_for_each(|i| {
                        inherit_return_from_call(analyzer, modifier_state.loc, *i)?;
                        Ok(())
                    })?;
                }
                Ok(())
            }
        })
    }

    /// Inherit the input changes from a function call
    fn inherit_input_changes(
        &mut self,
        loc: Loc,
        to_ctx: ContextNode,
        from_ctx: ContextNode,
        renamed_inputs: &BTreeMap<ContextVarNode, ContextVarNode>,
    ) -> Result<(), ExprErr> {
        if to_ctx != from_ctx {
            self.apply_to_edges(to_ctx, loc, &|analyzer, to_ctx, loc| {
                renamed_inputs
                    .iter()
                    .try_for_each(|(input_var, updated_var)| {
                        let new_input = analyzer.advance_var_in_ctx(
                            input_var.latest_version(analyzer),
                            loc,
                            to_ctx,
                        )?;
                        let latest_updated = updated_var.latest_version(analyzer);
                        if let Some(updated_var_range) =
                            latest_updated.range(analyzer).into_expr_err(loc)?
                        {
                            let res = new_input
                                .set_range_min(analyzer, updated_var_range.range_min())
                                .into_expr_err(loc);
                            let _ = analyzer.add_if_err(res);
                            let res = new_input
                                .set_range_max(analyzer, updated_var_range.range_max())
                                .into_expr_err(loc);
                            let _ = analyzer.add_if_err(res);
                            let res = new_input
                                .set_range_exclusions(
                                    analyzer,
                                    updated_var_range.range_exclusions(),
                                )
                                .into_expr_err(loc);
                            let _ = analyzer.add_if_err(res);
                        }
                        Ok(())
                    })
            })?;
        }
        Ok(())
    }

    /// Inherit the input changes from a function call
    fn modifier_inherit_return(&mut self, mod_ctx: ContextNode, fn_ctx: ContextNode) {
        let ret = fn_ctx.underlying(self).unwrap().ret.clone();
        mod_ctx.underlying_mut(self).unwrap().ret = ret;
    }

    /// Inherit the storage changes from a function call
    fn inherit_storage_changes(
        &mut self,
        loc: Loc,
        inheritor_ctx: ContextNode,
        grantor_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        if inheritor_ctx != grantor_ctx {
            return self.apply_to_edges(inheritor_ctx, loc, &|analyzer, inheritor_ctx, loc| {
                let vars = grantor_ctx.local_vars(analyzer);
                vars.iter().try_for_each(|old_var| {
                    let var = old_var.latest_version(analyzer);
                    let underlying = var.underlying(analyzer).into_expr_err(loc)?;
                    if var.is_storage(analyzer).into_expr_err(loc)? {
                        // println!(
                        //     "{} -- {} --> {}",
                        //     grantor_ctx.path(self),
                        //     underlying.name,
                        //     inheritor_ctx.path(self)
                        // );
                        if let Some(inheritor_var) =
                            inheritor_ctx.var_by_name(analyzer, &underlying.name)
                        {
                            let inheritor_var = inheritor_var.latest_version(analyzer);
                            if let Some(r) = underlying.ty.range(analyzer).into_expr_err(loc)? {
                                let new_inheritor_var = analyzer
                                    .advance_var_in_ctx(
                                        inheritor_var,
                                        underlying.loc.expect("No loc for val change"),
                                        inheritor_ctx,
                                    )
                                    .unwrap();
                                let _ = new_inheritor_var.set_range_min(analyzer, r.range_min());
                                let _ = new_inheritor_var.set_range_max(analyzer, r.range_max());
                                let _ = new_inheritor_var
                                    .set_range_exclusions(analyzer, r.range_exclusions());
                            }
                        } else {
                            let new_in_inheritor =
                                analyzer.add_node(Node::ContextVar(underlying.clone()));
                            analyzer.add_edge(
                                new_in_inheritor,
                                inheritor_ctx,
                                Edge::Context(ContextEdge::Variable),
                            );
                            analyzer.add_edge(
                                new_in_inheritor,
                                var,
                                Edge::Context(ContextEdge::InheritedVariable),
                            );
                        }
                    }
                    Ok(())
                })
            });
        }
        Ok(())
    }

    fn modifiers(
        &mut self,
        ctx: ContextNode,
        func: FunctionNode,
    ) -> Result<Vec<FunctionNode>, ExprErr> {
        use std::fmt::Write;
        let binding = func.underlying(self).unwrap().clone();
        let modifiers = binding.modifiers_as_base();
        if modifiers.is_empty() {
            Ok(vec![])
        } else {
            let res = modifiers
                .iter()
                .map(|modifier| {
                    assert_eq!(modifier.name.identifiers.len(), 1);
                    // construct arg string for function selector
                    let mut mod_name = format!("{}", modifier.name.identifiers[0]);
                    if let Some(args) = &modifier.args {
                        let args_str = args
                            .iter()
                            .map(|expr| {
                                let callee_ctx = ContextNode::from(
                                    self.add_node(Node::Context(
                                        Context::new_subctx(
                                            ctx,
                                            None,
                                            Loc::Implicit,
                                            None,
                                            None,
                                            false,
                                            self,
                                            None,
                                        )
                                        .into_expr_err(Loc::Implicit)?,
                                    )),
                                );
                                let _res = ctx.set_child_call(callee_ctx, self);
                                self.parse_ctx_expr(expr, callee_ctx)?;
                                let f: Vec<String> =
                                    self.take_from_edge(ctx, expr.loc(), &|analyzer, ctx, loc| {
                                        let ret = ctx
                                            .pop_expr(loc, analyzer)
                                            .into_expr_err(loc)?
                                            .unwrap();
                                        Ok(ret.try_as_func_input_str(analyzer))
                                    })?;

                                ctx.delete_child(self).into_expr_err(expr.loc())?;
                                Ok(f.first().unwrap().clone())
                            })
                            .collect::<Result<Vec<_>, ExprErr>>()?
                            .join(", ");
                        let _ = write!(mod_name, "{args_str}");
                    } else {
                        let _ = write!(mod_name, "()");
                    }
                    let _ = write!(mod_name, "");
                    let found: Option<FunctionNode> = ctx
                        .visible_modifiers(self)
                        .unwrap()
                        .iter()
                        .find(|modifier| modifier.name(self).unwrap() == mod_name)
                        .copied();
                    Ok(found)
                })
                .collect::<Result<Vec<Option<_>>, ExprErr>>()?
                .into_iter()
                .flatten()
                .collect::<Vec<_>>();
            Ok(res)
        }
    }

    fn set_modifiers(&mut self, func: FunctionNode, ctx: ContextNode) -> Result<(), ExprErr> {
        let modifiers = self.modifiers(ctx, func)?;
        modifiers
            .iter()
            .enumerate()
            .for_each(|(i, modifier)| self.add_edge(*modifier, func, Edge::FuncModifier(i)));
        func.underlying_mut(self).unwrap().modifiers_set = true;
        Ok(())
    }
}
