use crate::context::exprs::IntoExprErr;
use crate::context::func_call::{
    internal_call::InternalFuncCaller, intrinsic_call::IntrinsicFuncCaller,
    namespaced_call::NameSpaceFuncCaller,
};
use crate::context::ContextBuilder;
use crate::context::ExprErr;
use crate::ExprRet;
use shared::analyzer::AsDotStr;
use shared::analyzer::GraphLike;
use shared::context::*;
use std::collections::BTreeMap;

use shared::range::Range;
use solang_parser::pt::{Expression, Loc, NamedArgument, StorageLocation};

use crate::VarType;

use shared::{analyzer::AnalyzerLike, nodes::*, Edge, Node, NodeIdx};

pub mod internal_call;
pub mod intrinsic_call;
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
    ) -> Result<ExprRet, ExprErr> {
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
    ) -> Result<ExprRet, ExprErr> {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => {
                self.call_name_spaced_func(ctx, loc, member_expr, ident, input_exprs)
            }
            Variable(ident) => self.call_internal_func(ctx, loc, ident, func_expr, input_exprs),
            _ => {
                let ret = self.parse_ctx_expr(func_expr, ctx)?;
                self.match_intrinsic_fallback(loc, input_exprs, ret)
            }
        }
    }

    fn match_intrinsic_fallback(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        ret: ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Single((func_ctx, func_idx))
            | ExprRet::SingleLiteral((func_ctx, func_idx)) => {
                self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|ret| self.match_intrinsic_fallback(loc, input_exprs, ret))
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_intrinsic_fallback(loc, input_exprs, *w1)?),
                Box::new(self.match_intrinsic_fallback(loc, input_exprs, *w2)?),
            )),
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
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

    /// Setups up storage variables for a function call and calls it
    fn setup_fn_call(
        &mut self,
        loc: &Loc,
        inputs: &ExprRet,
        func_idx: NodeIdx,
        ctx: ContextNode,
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        // if we have a single match thats our function
        let var = match ContextVar::maybe_from_user_ty(self, *loc, func_idx) {
            Some(v) => v,
            None => panic!(
                "Could not create context variable from user type: {:?}",
                self.node(func_idx)
            ),
        };

        // TODO: this is probably wrong
        // if let Some(r) = var.fallback_range(self) {
        //     if var.storage.is_some() {
        //         if let Elem::Concrete(c) = r.range_max() {
        //             if let Some(size) = c.val.int_size() {
        //                 var.set_range_max(Elem::from(Concrete::Uint(size, 0.into())), None)
        //             }
        //         }
        //     }
        // }
        let new_cvarnode = self.add_node(Node::ContextVar(var));
        self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
        if let Some(func_node) = ContextVarNode::from(new_cvarnode)
            .ty(self)
            .into_expr_err(*loc)?
            .func_node(self)
        {
            self.func_call(ctx, *loc, inputs, func_node, func_call_str)
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
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        let params = func.params(self);
        let input_paths = input_paths.clone().flatten();
        match input_paths {
            ExprRet::Single((ctx, input_var)) | ExprRet::SingleLiteral((ctx, input_var)) => {
                // if we get a single var, we expect the func to only take a single
                // variable
                self.func_call_inner(
                    false,
                    ctx,
                    func,
                    loc,
                    vec![ContextVarNode::from(input_var).latest_version(self)],
                    params,
                    None,
                    func_call_str,
                )
            }
            ExprRet::Multi(ref inputs) => {
                // check if the inputs length matchs func params length
                // if they do, check that none are forks
                if inputs.len() == params.len() {
                    if !input_paths.has_fork() {
                        let input_vars = inputs
                            .iter()
                            .map(|expr_ret| {
                                let (_ctx, var) = expr_ret.expect_single(loc)?;
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
                            None,
                            func_call_str,
                        )
                    } else {
                        panic!(
                            "input has fork - need to flatten, {:?}, {:?}",
                            params,
                            input_paths.clone().flatten()
                        )
                    }
                } else {
                    panic!("Length mismatch: {inputs:?} {params:?}");
                }
            }
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.func_call(ctx, loc, &w1, func, func_call_str.clone())?),
                Box::new(self.func_call(ctx, loc, &w2, func, func_call_str)?),
            )),
            e => todo!("here: {:?}", e),
        }
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
        modifier_state: Option<ModifierState>,
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        let fn_ext = ctx.is_fn_ext(func_node, self).into_expr_err(loc)?;
        let callee_ctx = if entry_call {
            ctx
        } else {
            let callee_ctx = ContextNode::from(
                self.add_node(Node::Context(
                    Context::new_subctx(
                        ctx,
                        loc,
                        false,
                        Some(func_node),
                        fn_ext,
                        self,
                        modifier_state.clone(),
                    )
                    .into_expr_err(loc)?,
                )),
            );
            let res = ctx.add_child(callee_ctx, self).into_expr_err(loc);
            let _ = self.add_if_err(res);
            let ctx_fork = self.add_node(Node::FunctionCall);
            self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
            self.add_edge(ctx_fork, func_node, Edge::Context(ContextEdge::Call));
            self.add_edge(
                NodeIdx::from(callee_ctx.0),
                ctx_fork,
                Edge::Context(ContextEdge::Subcontext),
            );
            callee_ctx
        };

        let renamed_inputs = params
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
            .collect::<BTreeMap<_, ContextVarNode>>();

        if !func_node.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(func_node, ctx)?;
        }
        let mods = func_node.modifiers(self);
        if let Some(mod_state) = modifier_state {
            // we are iterating through modifiers
            if mod_state.num + 1 < mods.len() {
                // use the next modifier
                let mut mstate = mod_state;
                mstate.num += 1;
                self.call_modifier_for_fn(loc, callee_ctx, func_node, mstate, func_call_str)
            } else {
                // out of modifiers, execute the actual function call
                self.execute_call_inner(
                    loc,
                    ctx,
                    callee_ctx,
                    func_node,
                    renamed_inputs,
                    func_call_str,
                )
            }
        } else if !mods.is_empty() {
            // we have modifiers and havent executed them, start the process of executing them
            let state = ModifierState::new(0, loc, func_node, callee_ctx, ctx, renamed_inputs);
            self.call_modifier_for_fn(loc, callee_ctx, func_node, state, func_call_str)
        } else {
            // no modifiers, just execute the function
            self.execute_call_inner(
                loc,
                ctx,
                callee_ctx,
                func_node,
                renamed_inputs,
                func_call_str,
            )
        }
    }

    /// Actually executes the function
    #[tracing::instrument(level = "trace", skip_all)]
    fn execute_call_inner(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        func_node: FunctionNode,
        renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
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

            // update any requirements
            self.inherit_input_changes(loc, caller_ctx, callee_ctx, &renamed_inputs);
            self.inherit_storage_changes(caller_ctx, callee_ctx);

            Ok(self.ctx_rets(callee_ctx))
        } else {
            self.inherit_input_changes(loc, caller_ctx, callee_ctx, &renamed_inputs);
            self.inherit_storage_changes(caller_ctx, callee_ctx);
            Ok(ExprRet::Multi(
                func_node
                    .returns(self)
                    .iter()
                    .map(|ret| {
                        let underlying = ret.underlying(self).unwrap();
                        let mut var =
                            ContextVar::new_from_func_ret(callee_ctx, self, underlying.clone())
                                .unwrap()
                                .expect("No type for return variable?");
                        if let Some(func_call) = &func_call_str {
                            var.name =
                                format!("{}_{}", func_call, callee_ctx.new_tmp(self).unwrap());
                            var.display_name = func_call.to_string();
                        }
                        let node = self.add_node(Node::ContextVar(var));
                        self.add_edge(node, callee_ctx, Edge::Context(ContextEdge::Variable));
                        self.add_edge(node, callee_ctx, Edge::Context(ContextEdge::Return));
                        ExprRet::Single((caller_ctx, node))
                    })
                    .collect(),
            ))
        }
    }

    fn ctx_rets(&mut self, ctx: ContextNode) -> ExprRet {
        let forks = ctx.forks(self).unwrap();
        if !forks.is_empty() {
            assert!(forks.len() % 2 == 0);
            ExprRet::Multi(
                forks
                    .chunks(2)
                    .map(|fork_pairs| {
                        let w1 = self.ctx_rets(fork_pairs[0]);
                        let w2 = self.ctx_rets(fork_pairs[1]);
                        ExprRet::Fork(Box::new(w1), Box::new(w2))
                    })
                    .collect(),
            )
        } else {
            let rets = ctx
                .underlying(self)
                .unwrap()
                .ret
                .clone()
                .into_iter()
                .map(|(_, node)| ExprRet::Single((ctx, node.into())))
                .collect();
            ExprRet::Multi(rets)
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
        func_call_str: Option<String>,
    ) -> Result<ExprRet, ExprErr> {
        let mod_node = func_node.modifiers(self)[mod_state.num];
        tracing::trace!(
            "calling modifier {} for func {}",
            mod_node.name(self).into_expr_err(loc)?,
            func_node.name(self).into_expr_err(loc)?
        );
        let mod_ctx = ContextNode::from(
            self.add_node(Node::Context(
                Context::new_subctx(
                    func_ctx,
                    loc,
                    false,
                    Some(mod_node),
                    false,
                    self,
                    Some(mod_state.clone()),
                )
                .into_expr_err(loc)?,
            )),
        );
        let res = func_ctx.add_child(mod_ctx, self).into_expr_err(loc);
        let _ = self.add_if_err(res);
        let ctx_fork = self.add_node(Node::FunctionCall);
        self.add_edge(ctx_fork, func_ctx, Edge::Context(ContextEdge::Subcontext));
        self.add_edge(ctx_fork, mod_node, Edge::Context(ContextEdge::Call));
        self.add_edge(
            NodeIdx::from(mod_ctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );

        let input_exprs = func_node
            .modifier_input_vars(mod_state.num, self)
            .into_expr_err(loc)?;
        let inputs: Vec<ContextVarNode> = input_exprs
            .iter()
            .map(|expr| {
                let (_ctx, input) = self.parse_ctx_expr(expr, mod_ctx)?.expect_single(loc)?;
                Ok(input.into())
            })
            .collect::<Result<Vec<_>, ExprErr>>()?;

        let params = mod_node.params(self);
        let renamed_inputs = params
            .iter()
            .zip(inputs.iter())
            .filter_map(|(param, input)| {
                if let Some(name) = param.maybe_name(self).unwrap() {
                    let mut new_cvar = input.latest_version(self).underlying(self).unwrap().clone();
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

                    if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self).unwrap()) {
                        let ty = new_cvar.ty.clone();
                        if !ty.ty_eq(&param_ty, self).unwrap() {
                            if let Some(new_ty) = ty.try_cast(&param_ty, self).unwrap() {
                                new_cvar.ty = new_ty;
                            }
                        }
                    }

                    let node = ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                    if let (Some(r), Some(r2)) =
                        (node.range(self).unwrap(), param.range(self).unwrap())
                    {
                        let new_min = r.range_min().cast(r2.range_min());
                        let new_max = r.range_max().cast(r2.range_max());
                        let res = node.try_set_range_min(self, new_min).into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        let res = node.try_set_range_max(self, new_max).into_expr_err(loc);
                        let _ = self.add_if_err(res);
                        let res = node
                            .try_set_range_exclusions(self, r.exclusions)
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                    self.add_edge(node, mod_ctx, Edge::Context(ContextEdge::Variable));
                    Some((*input, node))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_, ContextVarNode>>();

        self.execute_call_inner(
            mod_node.underlying(self).into_expr_err(loc)?.loc,
            func_ctx,
            mod_ctx,
            mod_node,
            renamed_inputs,
            func_call_str,
        )
    }

    /// Resumes the parent function of a modifier
    #[tracing::instrument(level = "trace", skip_all)]
    fn resume_from_modifier(
        &mut self,
        ctx: ContextNode,
        modifier_state: ModifierState,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!(
            "resuming from modifier: {}",
            ctx.associated_fn_name(self)
                .into_expr_err(modifier_state.loc)?
        );
        // pass up the variable changes
        self.inherit_input_changes(
            modifier_state.loc,
            modifier_state.parent_ctx,
            ctx,
            &modifier_state.renamed_inputs,
        );
        self.inherit_storage_changes(modifier_state.parent_ctx, ctx);

        let mods = modifier_state.parent_fn.modifiers(self);
        if modifier_state.num + 1 < mods.len() {
            // use the next modifier
            let mut mstate = modifier_state;
            mstate.num += 1;
            self.call_modifier_for_fn(
                mods[mstate.num]
                    .underlying(self)
                    .into_expr_err(mstate.loc)?
                    .loc,
                ctx,
                mstate.parent_fn,
                mstate,
                None,
            )
        } else {
            // actually execute the parent function
            self.execute_call_inner(
                modifier_state.loc,
                modifier_state.parent_caller_ctx,
                modifier_state.parent_ctx,
                modifier_state.parent_fn,
                modifier_state.renamed_inputs,
                None,
            )
        }
    }

    /// Inherit the input changes from a function call
    fn inherit_input_changes(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        renamed_inputs: &BTreeMap<ContextVarNode, ContextVarNode>,
    ) {
        if caller_ctx != callee_ctx {
            renamed_inputs.iter().for_each(|(input_var, updated_var)| {
                let new_input = self
                    .advance_var_in_ctx(input_var.latest_version(self), loc, caller_ctx)
                    .unwrap();
                let latest_updated = updated_var.latest_version(self);
                if let Some(updated_var_range) = latest_updated.range(self).unwrap() {
                    let res = new_input
                        .set_range_min(self, updated_var_range.range_min())
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);
                    let res = new_input
                        .set_range_max(self, updated_var_range.range_max())
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);
                    let res = new_input
                        .set_range_exclusions(self, updated_var_range.range_exclusions())
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);
                }
            });
        }
    }

    /// Inherit the input changes from a function call
    fn modifier_inherit_return(&mut self, mod_ctx: ContextNode, fn_ctx: ContextNode) {
        let ret = fn_ctx.underlying(self).unwrap().ret.clone();
        mod_ctx.underlying_mut(self).unwrap().ret = ret;
    }

    /// Inherit the storage changes from a function call
    fn inherit_storage_changes(&mut self, inheritor_ctx: ContextNode, grantor_ctx: ContextNode) {
        if inheritor_ctx != grantor_ctx {
            let vars = grantor_ctx.local_vars(self);
            vars.iter().for_each(|old_var| {
                let var = old_var.latest_version(self);
                let underlying = var.underlying(self).unwrap();
                if var.is_storage(self).unwrap() {
                    // println!("{} -- {} --> {}", grantor_ctx.associated_fn_name(self), underlying.name, inheritor_ctx.associated_fn_name(self));
                    if let Some(inheritor_var) = inheritor_ctx.var_by_name(self, &underlying.name) {
                        let inheritor_var = inheritor_var.latest_version(self);
                        if let Some(r) = underlying.ty.range(self).unwrap() {
                            let new_inheritor_var = self
                                .advance_var_in_ctx(
                                    inheritor_var,
                                    underlying.loc.expect("No loc for val change"),
                                    inheritor_ctx,
                                )
                                .unwrap();
                            let _ = new_inheritor_var.set_range_min(self, r.range_min());
                            let _ = new_inheritor_var.set_range_max(self, r.range_max());
                            let _ =
                                new_inheritor_var.set_range_exclusions(self, r.range_exclusions());
                        }
                    } else {
                        let new_in_inheritor = self.add_node(Node::ContextVar(underlying.clone()));
                        self.add_edge(
                            new_in_inheritor,
                            inheritor_ctx,
                            Edge::Context(ContextEdge::Variable),
                        );
                    }
                }
            });
        }
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
                                let ret = self.parse_ctx_expr(expr, ctx)?;
                                Ok(ret.try_as_func_input_str(self))
                            })
                            .collect::<Result<Vec<_>, ExprErr>>()?
                            .join(", ");
                        let _ = write!(mod_name, "{args_str}");
                    }
                    let _ = write!(mod_name, "");

                    // println!("func modifiers: {},\n{:?},\n{:#?},\n{}", func.name(self), mod_name, ctx.visible_modifiers(self), ctx.visible_modifiers(self)[0].name(self));
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
