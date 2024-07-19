//! Traits & blanket implementations that facilitate performing modifier function calls.

use crate::{func_caller::FuncCaller, helper::CallerHelper, ContextBuilder};

use graph::{
    elem::Elem,
    nodes::{Concrete, Context, ContextNode, FunctionNode, ModifierState, SubContextKind},
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
        let _ = arena;
        let _ = loc;
        let _ = func_ctx;
        let _ = func_node;
        let _ = mod_state;
        todo!()
        // let mod_node = func_node.modifiers(self)[mod_state.num];
        // tracing::trace!(
        //     "calling modifier {} for func {}",
        //     mod_node.name(self).into_expr_err(loc)?,
        //     func_node.name(self).into_expr_err(loc)?
        // );

        // let input_exprs = func_node
        //     .modifier_input_vars(mod_state.num, self)
        //     .into_expr_err(loc)?;

        // input_exprs
        //     .iter()
        //     .try_for_each(|expr| self.parse_ctx_expr(arena, expr, func_ctx))?;
        // self.apply_to_edges(func_ctx, loc, arena, &|analyzer, arena, ctx, loc| {
        //     let input_paths = if input_exprs.is_empty() {
        //         ExprRet::Multi(vec![])
        //     } else {
        //         let Some(input_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //         else {
        //             return Err(ExprErr::NoRhs(
        //                 loc,
        //                 format!("No inputs to modifier, expected: {}", input_exprs.len()),
        //             ));
        //         };

        //         if matches!(input_paths, ExprRet::CtxKilled(_)) {
        //             ctx.push_expr(input_paths, analyzer).into_expr_err(loc)?;
        //             return Ok(());
        //         }
        //         input_paths
        //     };

        //     analyzer.func_call(
        //         arena,
        //         ctx,
        //         loc,
        //         &input_paths,
        //         mod_node,
        //         None,
        //         Some(mod_state.clone()),
        //     )
        // })
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
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func: FunctionNode,
    ) -> Result<Vec<FunctionNode>, ExprErr> {
        // use std::fmt::Write;
        let binding = func.underlying(self).unwrap().clone();
        let modifiers = binding.modifiers_as_base();
        if modifiers.is_empty() {
            Ok(vec![])
        } else {
            let _ = arena;
            let _ = ctx;
            todo!()
            // let res = modifiers
            //     .iter()
            //     .map(|modifier| {
            //         assert_eq!(modifier.name.identifiers.len(), 1);
            //         // construct arg string for function selector
            //         let mut mod_name = format!("{}", modifier.name.identifiers[0]);
            //         if let Some(args) = &modifier.args {
            //             let args_str = args
            //                 .iter()
            //                 .map(|expr| {
            //                     let subctx_kind = SubContextKind::new_dummy(ctx);
            //                     let callee_ctx =
            //                         Context::add_subctx(subctx_kind, Loc::Implicit, self, None)
            //                             .into_expr_err(Loc::Implicit)?;
            //                     let _res = ctx.set_child_call(callee_ctx, self);
            //                     self.parse_ctx_expr(arena, expr, callee_ctx)?;
            //                     let f: Vec<String> = self.take_from_edge(
            //                         ctx,
            //                         expr.loc(),
            //                         arena,
            //                         &|analyzer, arena, ctx, loc| {
            //                             let ret = ctx
            //                                 .pop_expr_latest(loc, analyzer)
            //                                 .into_expr_err(loc)?
            //                                 .unwrap();
            //                             Ok(ret.try_as_func_input_str(analyzer, arena))
            //                         },
            //                     )?;

            //                     ctx.delete_child(self).into_expr_err(expr.loc())?;
            //                     Ok(f.first().unwrap().clone())
            //                 })
            //                 .collect::<Result<Vec<_>, ExprErr>>()?
            //                 .join(", ");
            //             let _ = write!(mod_name, "{args_str}");
            //         } else {
            //             let _ = write!(mod_name, "()");
            //         }
            //         let _ = write!(mod_name, "");
            //         let found: Option<FunctionNode> = ctx
            //             .visible_modifiers(self)
            //             .unwrap()
            //             .iter()
            //             .find(|modifier| modifier.name(self).unwrap() == mod_name)
            //             .copied();
            //         Ok(found)
            //     })
            //     .collect::<Result<Vec<Option<_>>, ExprErr>>()?
            //     .into_iter()
            //     .flatten()
            //     .collect::<Vec<_>>();
            // Ok(res)
        }
    }

    /// Sets the modifiers for a function
    fn set_modifiers(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func: FunctionNode,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let modifiers = self.modifiers(arena, ctx, func)?;
        modifiers
            .iter()
            .enumerate()
            .for_each(|(i, modifier)| self.add_edge(*modifier, func, Edge::FuncModifier(i)));
        func.underlying_mut(self).unwrap().modifiers_set = true;
        Ok(())
    }
}
