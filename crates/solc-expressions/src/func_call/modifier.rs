//! Traits & blanket implementations that facilitate performing modifier function calls.

use crate::{
    func_call::internal_call::InternalFuncCaller, func_caller::FuncCaller, helper::CallerHelper,
    ContextBuilder,
};

use graph::{
    elem::Elem,
    nodes::{Concrete, Context, ContextNode, ExprRet, FunctionNode, ModifierState, SubContextKind},
    AnalyzerBackend, Edge, GraphBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> ModifierCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>
        + Sized
        + GraphBackend
        + FuncCaller
        + CallerHelper
{
}
/// A trait for dealing with modifier calls
pub trait ModifierCaller:
    GraphBackend
    + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>
    + Sized
    + FuncCaller
    + CallerHelper
{
    /// Calls a modifier for a function
    #[tracing::instrument(level = "trace", skip_all)]
    fn call_modifier_for_fn(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
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

        self.apply_to_edges(func_ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            if analyzer.debug_stack() {
                tracing::trace!(
                    "stack for getting modifier inputs: {}, ctx: {},",
                    mod_state
                        .parent_ctx
                        .debug_expr_stack_str(analyzer)
                        .into_expr_err(loc)?,
                    mod_state.parent_ctx.path(analyzer)
                );
            }

            let inputs = ExprRet::Multi(
                mod_state
                    .parent_ctx
                    .pop_n_latest_exprs(input_exprs.len(), loc, analyzer)
                    .into_expr_err(loc)?,
            );

            if analyzer.debug_stack() {
                tracing::trace!("modifier inputs: {}", inputs.debug_str(analyzer));
            }
            analyzer.func_call(
                arena,
                ctx,
                loc,
                &inputs,
                mod_node,
                None,
                Some(mod_state.clone()),
                None,
                false,
            )
        })
    }

    /// Resumes the parent function of a modifier
    #[tracing::instrument(level = "trace", skip_all)]
    fn resume_from_modifier(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        modifier_state: ModifierState,
    ) -> Result<(), ExprErr> {
        tracing::trace!(
            "resuming from modifier: {}",
            ctx.associated_fn_name(self)
                .into_expr_err(modifier_state.loc)?
        );

        let mods = modifier_state.parent_fn.modifiers(self);
        self.apply_to_edges(
            ctx,
            modifier_state.loc,
            arena,
            &|analyzer, arena, ctx, _loc| {
                if modifier_state.num + 1 < mods.len() {
                    // use the next modifier
                    let mut mstate = modifier_state.clone();
                    mstate.num += 1;

                    let loc = mods[mstate.num]
                        .underlying(analyzer)
                        .into_expr_err(mstate.loc)?
                        .loc;

                    let subctx_kind = SubContextKind::new_fn_call(
                        ctx,
                        Some(modifier_state.parent_ctx),
                        mods[mstate.num],
                        false,
                    );
                    let new_parent_subctx = Context::add_subctx(
                        subctx_kind,
                        loc,
                        analyzer,
                        Some(modifier_state.clone()),
                    )
                    .unwrap();

                    ctx.set_child_call(new_parent_subctx, analyzer)
                        .into_expr_err(modifier_state.loc)?;

                    analyzer.call_modifier_for_fn(
                        arena,
                        mods[mstate.num]
                            .underlying(analyzer)
                            .into_expr_err(mstate.loc)?
                            .loc,
                        new_parent_subctx,
                        mstate.parent_fn,
                        mstate,
                    )?;
                    Ok(())
                } else {
                    let subctx_kind = SubContextKind::new_fn_call(
                        ctx,
                        Some(modifier_state.parent_ctx),
                        modifier_state.parent_fn,
                        false,
                    );

                    let new_parent_subctx =
                        Context::add_subctx(subctx_kind, modifier_state.loc, analyzer, None)
                            .unwrap();
                    ctx.set_child_call(new_parent_subctx, analyzer)
                        .into_expr_err(modifier_state.loc)?;

                    // actually execute the parent function
                    analyzer.execute_call_inner(
                        arena,
                        modifier_state.loc,
                        ctx,
                        new_parent_subctx,
                        modifier_state.parent_fn,
                        None,
                    )
                }
            },
        )
    }

    fn modifiers(
        &mut self,
        ctx: ContextNode,
        func: FunctionNode,
    ) -> Result<Vec<FunctionNode>, ExprErr> {
        // use std::fmt::Write;
        let binding = func.underlying(self).unwrap().clone();

        let modifiers = binding.modifiers_as_base();
        if modifiers.is_empty() {
            Ok(vec![])
        } else {
            let mut mods = vec![];
            modifiers.iter().try_for_each(|modifier| {
                assert_eq!(modifier.name.identifiers.len(), 1);
                // // construct arg string for function selector
                let mod_name = format!("{}", modifier.name.identifiers[0]);
                let mod_loc = modifier.name.identifiers[0].loc;
                let is_constructor = func.is_constructor(self).into_expr_err(mod_loc)?;
                let mut found_mods = self.find_modifier(ctx, &mod_name, is_constructor).into_expr_err(mod_loc)?;
                match found_mods.len() {
                    0 => Err(ExprErr::FunctionNotFound(mod_loc, format!("Could not find modifier: {mod_name}"))),
                    1 => {
                        mods.push(found_mods.swap_remove(0));
                        Ok(())
                    }
                    n => Err(ExprErr::FunctionNotFound(mod_loc, format!("Could not find unique modifier: {mod_name}, found {n} modifiers with the same name"))),
                }
            })?;
            Ok(mods)
        }
    }

    /// Sets the modifiers for a function
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
