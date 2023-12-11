//! Helper traits & blanket implementations that help facilitate performing function calls.
use crate::{
    ContextBuilder, ExprErr, IntoExprErr,
};

use graph::{
    nodes::{
        CallFork, Context, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode,
        FunctionParamNode, FunctionReturnNode, ModifierState,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, Range, VarType,
};
use shared::{NodeIdx, StorageLocation};

use solang_parser::pt::{Expression, Loc};

use std::{
	cell::RefCell,
	collections::BTreeMap,
	rc::Rc
};

impl<T> CallerHelper for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Helper trait for performing function calls
pub trait CallerHelper: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
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
                            let new_min =
                                r.range_min().into_owned().cast(r2.range_min().into_owned());
                            let new_max =
                                r.range_max().into_owned().cast(r2.range_max().into_owned());
                            let res = node.try_set_range_min(self, new_min).into_expr_err(loc);
                            self.add_if_err(res);
                            let res = node.try_set_range_max(self, new_max).into_expr_err(loc);
                            self.add_if_err(res);
                            let res = node
                                .try_set_range_exclusions(self, r.exclusions)
                                .into_expr_err(loc);
                            self.add_if_err(res);
                        }
                        callee_ctx.add_var(node, self).unwrap();
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

    #[tracing::instrument(level = "trace", skip_all)]
    /// Parses input expressions into [`ExprRet`]s and adds them to the expr ret stack
    fn parse_inputs(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        inputs: &[Expression],
    ) -> Result<(), ExprErr> {
        let append = if ctx.underlying(self).into_expr_err(loc)?.tmp_expr.is_empty() {
            Rc::new(RefCell::new(true))
        } else {
            Rc::new(RefCell::new(false))
        };

        inputs.iter().try_for_each(|input| {
            self.parse_ctx_expr(input, ctx)?;
            self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(
                        loc,
                        "Inputs did not have left hand sides".to_string(),
                    ));
                };
                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
                if *append.borrow() {
                    ctx.append_tmp_expr(ret, analyzer).into_expr_err(loc)
                } else {
                    *append.borrow_mut() = true;
                    ctx.push_tmp_expr(ret, analyzer).into_expr_err(loc)
                }
            })
        })?;
        if !inputs.is_empty() {
            self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                let Some(ret) = ctx.pop_tmp_expr(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoLhs(
                        loc,
                        "Inputs did not have left hand sides".to_string(),
                    ));
                };
                ctx.push_expr(ret, analyzer).into_expr_err(loc)
            })
        } else {
            Ok(())
        }
    }

    /// Creates a new context for a call
    fn create_call_ctx(
        &mut self,
        curr_ctx: ContextNode,
        loc: Loc,
        func_node: FunctionNode,
        modifier_state: Option<ModifierState>,
    ) -> Result<ContextNode, ExprErr> {
        let fn_ext = curr_ctx.is_fn_ext(func_node, self).into_expr_err(loc)?;
        let ctx = Context::new_subctx(
            curr_ctx,
            None,
            loc,
            None,
            Some(func_node),
            fn_ext,
            self,
            modifier_state,
        )
        .into_expr_err(loc)?;
        let callee_ctx = ContextNode::from(self.add_node(Node::Context(ctx)));
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
                            let param_ty = VarType::try_from_idx(self, (*param).into()).unwrap();
                            let input_ty = ContextVarNode::from(*input).ty(self).unwrap();
                            if param_ty.ty_eq(input_ty, self).unwrap() {
                                true
                            } else if literals[i] {
                                let possibilities = ContextVarNode::from(*input)
                                    .ty(self)
                                    .unwrap()
                                    .possible_builtins_from_ty_inf(self);
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

    /// Handle returns for a function call
    fn ctx_rets(
        &mut self,
        loc: Loc,
        caller_ctx: ContextNode,
        callee_ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "Handling function call return for: {}, {}, depth: {:?}, {:?}",
            caller_ctx.path(self),
            callee_ctx.path(self),
            caller_ctx.depth(self),
            callee_ctx.depth(self),
        );
        match callee_ctx.underlying(self).into_expr_err(loc)?.child {
            Some(CallFork::Fork(w1, w2)) => {
                self.ctx_rets(loc, caller_ctx, w1)?;
                self.ctx_rets(loc, caller_ctx, w2)?;
                Ok(())
            }
            Some(CallFork::Call(c))
                if c.underlying(self).into_expr_err(loc)?.depth
                    >= caller_ctx.underlying(self).into_expr_err(loc)?.depth =>
            {
                // follow rabbit hole
                self.ctx_rets(loc, caller_ctx, c)?;
                Ok(())
            }
            _ => {
                if callee_ctx.is_killed(self).into_expr_err(loc)? {
                    return Ok(());
                }
                let callee_depth = callee_ctx.underlying(self).into_expr_err(loc)?.depth;
                let caller_depth = caller_ctx.underlying(self).into_expr_err(loc)?.depth;
                if callee_depth != caller_depth {
                    let ctx = Context::new_subctx(
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
                    .unwrap();
                    let ret_subctx = ContextNode::from(self.add_node(Node::Context(ctx)));
                    self.add_edge(ret_subctx, caller_ctx, Edge::Context(ContextEdge::Continue));

                    let res = callee_ctx
                        .set_child_call(ret_subctx, self)
                        .into_expr_err(loc);
                    let _ = self.add_if_err(res);

                    let mut rets = callee_ctx.underlying(self).unwrap().ret.clone();

                    if rets.is_empty() {
                        let func_rets: Vec<FunctionReturnNode> = callee_ctx
                            .associated_fn(self)
                            .into_expr_err(loc)?
                            .returns(self)
                            .collect();
                        func_rets
                            .iter()
                            .filter_map(|ret| {
                                let n: String = ret.maybe_name(self).ok()??;
                                let ret_loc: Loc = ret.loc(self).ok()?;
                                Some((n, ret_loc))
                            })
                            .collect::<Vec<_>>()
                            .into_iter()
                            .try_for_each(|(name, ret_loc)| {
                                if let Some(cvar) = callee_ctx
                                    .var_by_name_or_recurse(self, &name)
                                    .into_expr_err(loc)?
                                {
                                    let cvar = cvar.latest_version(self);
                                    // let ret_loc = ret.loc(self).into_expr_err(loc)?;
                                    callee_ctx
                                        .add_return_node(ret_loc, cvar, self)
                                        .into_expr_err(loc)?;
                                    self.add_edge(
                                        cvar,
                                        callee_ctx,
                                        Edge::Context(ContextEdge::Return),
                                    );
                                }
                                Ok(())
                            })?;

                        // add unnamed rets
                        func_rets
                            .into_iter()
                            .filter(|ret| ret.maybe_name(self).unwrap().is_none())
                            .collect::<Vec<_>>()
                            .iter()
                            .try_for_each(|ret| {
                                let ret_loc = ret.loc(self).into_expr_err(loc)?;
                                let cvar = ContextVar::new_from_func_ret(
                                    callee_ctx,
                                    self,
                                    ret.underlying(self).into_expr_err(loc)?.clone(),
                                )
                                .into_expr_err(loc)?
                                .unwrap();
                                let cvar =
                                    ContextVarNode::from(self.add_node(Node::ContextVar(cvar)));
                                callee_ctx.add_var(cvar, self).into_expr_err(loc)?;
                                self.add_edge(
                                    cvar,
                                    callee_ctx,
                                    Edge::Context(ContextEdge::Variable),
                                );
                                callee_ctx
                                    .add_return_node(ret_loc, cvar, self)
                                    .into_expr_err(loc)?;
                                self.add_edge(cvar, callee_ctx, Edge::Context(ContextEdge::Return));
                                Ok(())
                            })?;
                        rets = callee_ctx.underlying(self).unwrap().ret.clone();
                    }

                    let handle_rets = rets.iter().all(|(_, node)| node.is_some());
                    if handle_rets {
                        let ret = rets
                            .into_iter()
                            .enumerate()
                            .map(|(i, (_, node))| {
                                let tmp_ret = node
                                    .unwrap()
                                    .as_tmp(
                                        callee_ctx.underlying(self).unwrap().loc,
                                        ret_subctx,
                                        self,
                                    )
                                    .unwrap();
                                tmp_ret.underlying_mut(self).into_expr_err(loc)?.is_return = true;
                                tmp_ret
                                    .underlying_mut(self)
                                    .into_expr_err(loc)?
                                    .display_name = format!(
                                    "{}.{}",
                                    callee_ctx.associated_fn_name(self).unwrap(),
                                    i
                                );
                                ret_subctx.add_var(tmp_ret, self).into_expr_err(loc)?;
                                self.add_edge(
                                    tmp_ret,
                                    ret_subctx,
                                    Edge::Context(ContextEdge::Variable),
                                );
                                Ok(ExprRet::Single(tmp_ret.into()))
                            })
                            .collect::<Result<_, ExprErr>>()?;
                        ret_subctx
                            .push_expr(ExprRet::Multi(ret), self)
                            .into_expr_err(loc)?;
                    }
                    Ok(())
                } else {
                    let mut rets = callee_ctx.underlying(self).unwrap().ret.clone();

                    if rets.is_empty() {
                        callee_ctx
                            .associated_fn(self)
                            .into_expr_err(loc)?
                            .returns(self)
                            .filter_map(|ret| {
                                let n: String = ret.maybe_name(self).ok()??;
                                let ret_loc: Loc = ret.loc(self).ok()?;
                                Some((n, ret_loc))
                            })
                            .collect::<Vec<_>>()
                            .into_iter()
                            .try_for_each(|(name, ret_loc)| {
                                if let Some(cvar) = callee_ctx
                                    .var_by_name_or_recurse(self, &name)
                                    .into_expr_err(loc)?
                                {
                                    let cvar = cvar.latest_version(self);
                                    // let ret_loc = ret.loc(self).into_expr_err(loc)?;
                                    callee_ctx
                                        .add_return_node(ret_loc, cvar, self)
                                        .into_expr_err(loc)?;
                                    self.add_edge(
                                        cvar,
                                        callee_ctx,
                                        Edge::Context(ContextEdge::Return),
                                    );
                                }
                                Ok(())
                            })?;
                        rets = callee_ctx.underlying(self).unwrap().ret.clone();
                    }
                    if rets.iter().all(|(_, node)| node.is_some()) {
                        callee_ctx
                            .push_expr(
                                ExprRet::Multi(
                                    rets.iter()
                                        .map(|(_, node)| ExprRet::Single((node.unwrap()).into()))
                                        .collect(),
                                ),
                                self,
                            )
                            .into_expr_err(loc)
                    } else {
                        Ok(())
                    }
                }
            }
        }
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
                                .set_range_min(analyzer, updated_var_range.range_min().into_owned())
                                .into_expr_err(loc);
                            let _ = analyzer.add_if_err(res);
                            let res = new_input
                                .set_range_max(analyzer, updated_var_range.range_max().into_owned())
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
                let vars = grantor_ctx.local_vars(analyzer).clone();
                vars.iter().try_for_each(|(name, old_var)| {
                    let var = old_var.latest_version(analyzer);
                    let underlying = var.underlying(analyzer).into_expr_err(loc)?;
                    if var.is_storage(analyzer).into_expr_err(loc)? {
                        if let Some(inheritor_var) = inheritor_ctx.var_by_name(analyzer, name) {
                            let inheritor_var = inheritor_var.latest_version(analyzer);
                            if let Some(r) = underlying.ty.range(analyzer).into_expr_err(loc)? {
                                let new_inheritor_var = analyzer
                                    .advance_var_in_ctx(
                                        inheritor_var,
                                        underlying.loc.expect("No loc for val change"),
                                        inheritor_ctx,
                                    )
                                    .unwrap();
                                let _ = new_inheritor_var
                                    .set_range_min(analyzer, r.range_min().into_owned());
                                let _ = new_inheritor_var
                                    .set_range_max(analyzer, r.range_max().into_owned());
                                let _ = new_inheritor_var
                                    .set_range_exclusions(analyzer, r.range_exclusions());
                            }
                        } else {
                            let new_in_inheritor =
                                analyzer.add_node(Node::ContextVar(underlying.clone()));
                            inheritor_ctx
                                .add_var(new_in_inheritor.into(), analyzer)
                                .into_expr_err(loc)?;
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
}