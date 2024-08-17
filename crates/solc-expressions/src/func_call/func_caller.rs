//! Traits & blanket implementations that facilitate performing various forms of function calls.

use crate::{func_call::modifier::ModifierCaller, helper::CallerHelper, ContextBuilder, Flatten};

use graph::{
    elem::Elem,
    nodes::{
        Concrete, Context, ContextNode, ContextVar, ContextVarNode, ContractId, EnvCtx, ExprRet,
        FunctionNode, FunctionParamNode, ModifierState, SubContextKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{CodeLocation, Expression, Loc};

impl<T> FuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}
/// A trait for calling a function
pub trait FuncCaller:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Matches the input kinds and performs the call
    fn func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        input_paths: &ExprRet,
        func: FunctionNode,
        func_call_str: Option<&str>,
        modifier_state: Option<ModifierState>,
        msg: Option<EnvCtx>,
        ext_target: Option<ContractId>,
        try_catch: bool,
    ) -> Result<(), ExprErr> {
        let params = func.params(self);
        let input_paths = input_paths.clone().flatten();
        if input_paths.has_killed() {
            return ctx
                .kill(self, loc, input_paths.killed_kind().unwrap())
                .into_expr_err(loc);
        }
        match input_paths {
            ExprRet::Single(input_var) | ExprRet::SingleLiteral(input_var) => {
                // if we get a single var, we expect the func to only take a single
                // variable
                let inputs =
                    vec![ContextVarNode::from(input_var)
                        .latest_version_or_inherited_in_ctx(ctx, self)];
                self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                    analyzer.func_call_inner(
                        arena,
                        false,
                        ctx,
                        func,
                        loc,
                        &inputs,
                        &params,
                        func_call_str,
                        &modifier_state,
                        msg.clone(),
                        ext_target,
                        try_catch,
                    )
                })
            }
            ExprRet::Multi(ref inputs) => {
                if ExprRet::Multi(inputs.to_vec()).flatten().has_killed() {
                    return ctx
                        .kill(
                            self,
                            loc,
                            ExprRet::Multi(inputs.to_vec()).killed_kind().unwrap(),
                        )
                        .into_expr_err(loc);
                }
                // check if the inputs length matchs func params length
                // if they do, check that none are forks
                if inputs.len() == params.len() {
                    let input_vars = inputs
                        .iter()
                        .map(|expr_ret| {
                            let var = expr_ret.expect_single().into_expr_err(loc)?;
                            Ok(ContextVarNode::from(var)
                                .latest_version_or_inherited_in_ctx(ctx, self))
                        })
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        analyzer.func_call_inner(
                            arena,
                            false,
                            ctx,
                            func,
                            loc,
                            &input_vars,
                            &params,
                            func_call_str,
                            &modifier_state,
                            msg.clone(),
                            ext_target,
                            try_catch,
                        )
                    })
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
            ExprRet::Null => self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                analyzer.func_call_inner(
                    arena,
                    false,
                    ctx,
                    func,
                    loc,
                    &[],
                    &params,
                    func_call_str,
                    &modifier_state,
                    msg.clone(),
                    ext_target,
                    try_catch,
                )
            }),
            e => todo!("here: {:?}", e),
        }
    }

    /// Checks if there are any modifiers and executes them prior to executing the function
    #[tracing::instrument(level = "trace", skip_all)]
    fn func_call_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        entry_call: bool,
        ctx: ContextNode,
        func_node: FunctionNode,
        loc: Loc,
        inputs: &[ContextVarNode],
        params: &[FunctionParamNode],
        func_call_str: Option<&str>,
        modifier_state: &Option<ModifierState>,
        env: Option<EnvCtx>,
        ext_target: Option<ContractId>,
        try_catch: bool,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "Calling function: {} in context: {}",
            func_node.name(self).unwrap(),
            ctx.path(self)
        );
        if !entry_call {
            // if let Ok(true) = self.apply(arena, ctx, loc, func_node, params, inputs, &mut vec![]) {
            //     return Ok(());
            // }
        }

        // pseudocode:
        //  1. Create context for the call
        //  2. Check for modifiers
        //  3. Call modifier 0, then 1, then 2, ... then N.
        //  4. Call this function
        //  5. Finish modifier N.. then 2, then 1, then 0
        let callee_ctx = if entry_call {
            ctx
        } else {
            self.create_call_ctx(ctx, loc, func_node, modifier_state.clone(), ext_target)?
        };

        if entry_call || ext_target.is_some() {
            self.add_env(callee_ctx, func_node, env, loc)?;
        }

        // handle remapping of variable names and bringing variables into the new context
        let renamed_inputs =
            self.map_inputs_to_params(arena, loc, entry_call, params, inputs, callee_ctx)?;

        // begin modifier handling by making sure modifiers were set
        if !func_node.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(func_node, ctx)?;
        }

        // get modifiers
        let mods = func_node.modifiers(self);
        let modifiers_as_base = func_node
            .underlying(self)
            .into_expr_err(loc)?
            .modifiers_as_base()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        modifiers_as_base.iter().rev().for_each(|modifier| {
            // We need to get the inputs for the modifier call, but
            // the expressions are not part of the function body so
            // we need to reset the parse index in the function context
            // after we parse the inputs
            let Some(args) = &modifier.args else {
                return;
            };
            let curr_parse_idx = callee_ctx.parse_idx(self);
            args.iter()
                .for_each(|expr| self.traverse_expression(expr, Some(false)));
            self.interpret(callee_ctx, loc, arena);
            callee_ctx.underlying_mut(self).unwrap().parse_idx = curr_parse_idx;
        });
        let is_constructor = func_node.is_constructor(self).into_expr_err(loc)?;
        self.apply_to_edges(
            callee_ctx,
            loc,
            arena,
            &|analyzer, arena, callee_ctx, loc| {
                if is_constructor {
                    let mut state = ModifierState::new(
                        0,
                        loc,
                        func_node,
                        callee_ctx,
                        ctx,
                        renamed_inputs.clone(),
                        try_catch,
                    );
                    for _ in 0..mods.len() {
                        analyzer.call_modifier_for_fn(
                            arena,
                            loc,
                            callee_ctx,
                            func_node,
                            state.clone(),
                        )?;
                        state.num += 1;
                    }

                    analyzer.execute_call_inner(
                        arena,
                        loc,
                        ctx,
                        callee_ctx,
                        func_node,
                        func_call_str,
                        try_catch,
                    )
                } else if let Some(mod_state) =
                    &ctx.underlying(analyzer).into_expr_err(loc)?.modifier_state
                {
                    // we are iterating through modifiers
                    if mod_state.num + 1 < mods.len() {
                        // use the next modifier
                        let mut mstate = mod_state.clone();
                        mstate.num += 1;
                        analyzer.call_modifier_for_fn(arena, loc, callee_ctx, func_node, mstate)
                    } else {
                        // out of modifiers, execute the actual function call
                        analyzer.execute_call_inner(
                            arena,
                            loc,
                            ctx,
                            callee_ctx,
                            func_node,
                            func_call_str,
                            try_catch,
                        )
                    }
                } else if !mods.is_empty() {
                    // we have modifiers and havent executed them, start the process of executing them
                    let state = ModifierState::new(
                        0,
                        loc,
                        func_node,
                        callee_ctx,
                        ctx,
                        renamed_inputs.clone(),
                        try_catch,
                    );
                    analyzer.call_modifier_for_fn(arena, loc, callee_ctx, func_node, state)
                } else {
                    // no modifiers, just execute the function
                    analyzer.execute_call_inner(
                        arena,
                        loc,
                        ctx,
                        callee_ctx,
                        func_node,
                        func_call_str,
                        try_catch,
                    )
                }
            },
        )
    }

    /// Actually executes the function
    // #[tracing::instrument(level = "trace", skip_all)]
    fn execute_call_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
        func_node: FunctionNode,
        func_call_str: Option<&str>,
        try_catch: bool,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "executing: {}, try_catch: {try_catch}",
            func_node.name(self).into_expr_err(loc)?
        );
        if let Some(body) = func_node.underlying(self).into_expr_err(loc)?.body.clone() {
            // add return nodes into the subctx
            let mut ret_vars = vec![];
            #[allow(clippy::unnecessary_to_owned)]
            func_node.returns(arena, self).into_iter().for_each(|ret| {
                if let Some(var) =
                    ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).unwrap().clone())
                {
                    let cvar = self.add_node(var);
                    callee_ctx.add_var(cvar.into(), self).unwrap();
                    self.add_edge(cvar, callee_ctx, Edge::Context(ContextEdge::Variable));
                    ret_vars.push(cvar);
                }
            });

            // parse the function body
            self.traverse_statement(&body, None);
            self.interpret(callee_ctx, body.loc(), arena);
            if let Some(mod_state) = &callee_ctx
                .underlying(self)
                .into_expr_err(loc)?
                .modifier_state
                .clone()
            {
                if mod_state.num == 0 {
                    return self.ctx_rets(
                        arena,
                        loc,
                        mod_state.parent_caller_ctx,
                        callee_ctx,
                        try_catch,
                    );
                }
            }

            if callee_ctx != caller_ctx {
                self.ctx_rets(arena, loc, caller_ctx, callee_ctx, try_catch)
            } else {
                Ok(())
            }
        } else {
            let subctx_kind = SubContextKind::new_fn_ret(callee_ctx, caller_ctx);
            let ret_subctx = Context::add_subctx(
                subctx_kind,
                loc,
                self,
                caller_ctx
                    .underlying(self)
                    .into_expr_err(loc)?
                    .modifier_state
                    .clone(),
                caller_ctx.contract_id(self).into_expr_err(loc)?,
                true,
            )
            .unwrap();

            let res = callee_ctx
                .set_child_call(ret_subctx, self)
                .into_expr_err(loc);
            let _ = self.add_if_err(res);
            self.apply_to_edges(callee_ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                #[allow(clippy::unnecessary_to_owned)]
                func_node
                    .returns(arena, analyzer)
                    .into_iter()
                    .try_for_each(|ret| {
                        let underlying = ret.underlying(analyzer).unwrap();
                        let mut var =
                            ContextVar::new_from_func_ret(ctx, analyzer, underlying.clone())
                                .unwrap()
                                .expect("No type for return variable?");
                        if let Some(func_call) = &func_call_str {
                            var.name =
                                format!("{}_{}", func_call, callee_ctx.new_tmp(analyzer).unwrap());
                            var.display_name = func_call.to_string();
                        }

                        if ctx.contains_var(&var.name, analyzer).into_expr_err(loc)? {
                            var.name = format!(
                                "{}_ret{}",
                                var.name,
                                ctx.new_tmp(analyzer).into_expr_err(loc)?
                            );
                            var.display_name.clone_from(&var.name);
                        }

                        let node = analyzer.add_node(Node::ContextVar(var));
                        ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Return));

                        let as_var = ContextVarNode::from(node);
                        as_var.maybe_add_fields(analyzer).into_expr_err(loc)?;
                        as_var
                            .maybe_add_len_inplace(analyzer, arena, ctx, loc)
                            .into_expr_err(loc)?;

                        ctx.push_expr(ExprRet::Single(node), analyzer)
                            .into_expr_err(loc)?;
                        Ok(())
                    })
            })
        }
    }
}
