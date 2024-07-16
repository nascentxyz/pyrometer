//! Traits & blanket implementations that facilitate performing various forms of function calls.

use crate::{
    func_call::{apply::FuncApplier, modifier::ModifierCaller},
    helper::CallerHelper,
    internal_call::InternalFuncCaller,
    intrinsic_call::IntrinsicFuncCaller,
    namespaced_call::NameSpaceFuncCaller,
    ContextBuilder, ExpressionParser, Flatten,
};

use graph::{
    elem::Elem,
    nodes::{
        Concrete, Context, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode,
        FunctionParamNode, ModifierState, SubContextKind,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node,
};
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{CodeLocation, Expression, Loc, NamedArgument};

use std::collections::BTreeMap;

#[derive(Debug)]
pub enum NamedOrUnnamedArgs<'a> {
    Named(&'a [NamedArgument]),
    Unnamed(&'a [Expression]),
}

impl<'a> NamedOrUnnamedArgs<'a> {
    pub fn named_args(&self) -> Option<&'a [NamedArgument]> {
        match self {
            NamedOrUnnamedArgs::Named(inner) => Some(inner),
            _ => None,
        }
    }

    pub fn unnamed_args(&self) -> Option<&'a [Expression]> {
        match self {
            NamedOrUnnamedArgs::Unnamed(inner) => Some(inner),
            _ => None,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            NamedOrUnnamedArgs::Unnamed(inner) => inner.len(),
            NamedOrUnnamedArgs::Named(inner) => inner.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        match self {
            NamedOrUnnamedArgs::Unnamed(inner) => inner.len() == 0,
            NamedOrUnnamedArgs::Named(inner) => inner.len() == 0,
        }
    }

    pub fn exprs(&self) -> Vec<Expression> {
        match self {
            NamedOrUnnamedArgs::Unnamed(inner) => inner.to_vec(),
            NamedOrUnnamedArgs::Named(inner) => inner.iter().map(|i| i.expr.clone()).collect(),
        }
    }

    pub fn parse(
        &self,
        arena: &mut RangeArena<Elem<Concrete>>,
        analyzer: &mut (impl AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized),
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        unreachable!("should not exist");
    }

    pub fn parse_n(
        &self,
        arena: &mut RangeArena<Elem<Concrete>>,
        n: usize,
        analyzer: &mut (impl AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized),
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        unreachable!("should not exist");
    }

    pub fn order(&self, inputs: ExprRet, ordered_params: Vec<String>) -> ExprRet {
        if inputs.len() < 2 {
            inputs
        } else {
            match self {
                NamedOrUnnamedArgs::Unnamed(_inner) => inputs,
                NamedOrUnnamedArgs::Named(inner) => ExprRet::Multi(
                    ordered_params
                        .iter()
                        .map(|param| {
                            let index = inner
                                .iter()
                                .enumerate()
                                .find(|(_i, arg)| &arg.name.name == param)
                                .unwrap()
                                .0;
                            match &inputs {
                                ExprRet::Multi(inner) => inner[index].clone(),
                                _ => panic!("Mismatched ExprRet type"),
                            }
                        })
                        .collect(),
                ),
            }
        }
    }
}

impl<T> FuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend
{
}
/// A trait for calling a function
pub trait FuncCaller:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    #[tracing::instrument(level = "trace", skip_all)]
    /// Perform a function call with named inputs
    fn named_fn_call_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        func_expr: &Expression,
        input_exprs: &[NamedArgument],
    ) -> Result<(), ExprErr> {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => self.call_name_spaced_func(
                arena,
                ctx,
                loc,
                member_expr,
                ident,
                NamedOrUnnamedArgs::Named(input_exprs),
            ),
            Variable(ident) => self.call_internal_named_func(arena, ctx, loc, ident, input_exprs),
            e => Err(ExprErr::IntrinsicNamedArgs(
                *loc,
                format!("Cannot call intrinsic functions with named arguments. Call: {e:?}"),
            )),
        }
    }
    #[tracing::instrument(level = "trace", skip_all)]
    /// Perform a function call
    fn fn_call_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        func_expr: &Expression,
        input_exprs: &[Expression],
    ) -> Result<(), ExprErr> {
        use solang_parser::pt::Expression::*;
        match func_expr {
            MemberAccess(loc, member_expr, ident) => self.call_name_spaced_func(
                arena,
                ctx,
                loc,
                member_expr,
                ident,
                NamedOrUnnamedArgs::Unnamed(input_exprs),
            ),
            Variable(ident) => self.call_internal_func(
                arena,
                ctx,
                loc,
                ident,
                func_expr,
                NamedOrUnnamedArgs::Unnamed(input_exprs),
            ),
            _ => {
                self.parse_ctx_expr(arena, func_expr, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "Function call to nonexistent function".to_string(),
                        ));
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.match_intrinsic_fallback(
                        arena,
                        ctx,
                        &loc,
                        &NamedOrUnnamedArgs::Unnamed(input_exprs),
                        ret,
                    )
                })
            }
        }
    }

    /// Perform an intrinsic function call
    fn match_intrinsic_fallback(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        input_exprs: &NamedOrUnnamedArgs,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(func_idx) | ExprRet::SingleLiteral(func_idx) => {
                self.intrinsic_func_call(arena, loc, input_exprs, func_idx, ctx)
            }
            ExprRet::Multi(inner) => inner.into_iter().try_for_each(|ret| {
                self.match_intrinsic_fallback(arena, ctx, loc, input_exprs, ret)
            }),
            ExprRet::CtxKilled(kind) => ctx.kill(self, *loc, kind).into_expr_err(*loc),
            ExprRet::Null => Ok(()),
        }
    }

    /// Setups up storage variables for a function call and calls it
    fn setup_fn_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
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

        let new_cvarnode = self.add_node(var);
        ctx.add_var(new_cvarnode.into(), self).into_expr_err(*loc)?;
        self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
        if let Some(func_node) = ContextVarNode::from(new_cvarnode)
            .ty(self)
            .into_expr_err(*loc)?
            .func_node(self)
        {
            self.func_call(arena, ctx, *loc, inputs, func_node, func_call_str, None)
        } else {
            unreachable!()
        }
    }

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
    ) -> Result<(), ExprErr> {
        if !entry_call {
            if let Ok(true) = self.apply(arena, ctx, loc, func_node, params, inputs, &mut vec![]) {
                return Ok(());
            }
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
            self.create_call_ctx(ctx, loc, func_node, modifier_state.clone())?
        };

        // handle remapping of variable names and bringing variables into the new context
        let renamed_inputs =
            self.map_inputs_to_params(arena, loc, entry_call, params, inputs, callee_ctx)?;

        // begin modifier handling by making sure modifiers were set
        if !func_node.modifiers_set(self).into_expr_err(loc)? {
            self.set_modifiers(arena, func_node, ctx)?;
        }

        // get modifiers
        let mods = func_node.modifiers(self);
        self.apply_to_edges(
            callee_ctx,
            loc,
            arena,
            &|analyzer, arena, callee_ctx, loc| {
                if let Some(mod_state) =
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
                            &renamed_inputs,
                            func_call_str,
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
                        &renamed_inputs,
                        func_call_str,
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
        _renamed_inputs: &BTreeMap<ContextVarNode, ContextVarNode>,
        func_call_str: Option<&str>,
    ) -> Result<(), ExprErr> {
        tracing::trace!("executing: {}", func_node.name(self).into_expr_err(loc)?);
        if let Some(body) = func_node.underlying(self).into_expr_err(loc)?.body.clone() {
            // add return nodes into the subctx
            #[allow(clippy::unnecessary_to_owned)]
            func_node.returns(arena, self).into_iter().for_each(|ret| {
                if let Some(var) =
                    ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).unwrap().clone())
                {
                    let cvar = self.add_node(var);
                    callee_ctx.add_var(cvar.into(), self).unwrap();
                    self.add_edge(cvar, callee_ctx, Edge::Context(ContextEdge::Variable));
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
                    return self.ctx_rets(arena, loc, mod_state.parent_caller_ctx, callee_ctx);
                }
            }

            if callee_ctx != caller_ctx {
                self.ctx_rets(arena, loc, caller_ctx, callee_ctx)
            } else {
                Ok(())
            }
        } else {
            let subctx_kind = SubContextKind::new_fn_ret(callee_ctx, caller_ctx);
            let ret_ctx = Context::new_subctx(
                subctx_kind,
                loc,
                self,
                caller_ctx
                    .underlying(self)
                    .into_expr_err(loc)?
                    .modifier_state
                    .clone(),
            )
            .unwrap();
            let ret_subctx = ContextNode::from(self.add_node(Node::Context(ret_ctx)));

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
                        ctx.push_expr(ExprRet::Single(node), analyzer)
                            .into_expr_err(loc)?;
                        Ok(())
                    })
            })
        }
    }
}
