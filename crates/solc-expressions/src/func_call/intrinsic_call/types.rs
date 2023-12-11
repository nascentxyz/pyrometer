use crate::{
    ContextBuilder, ExprErr, FuncCaller, IntoExprErr,
};

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, ContextNode, ContextVar, ContextVarNode, ExprRet, TyNode,
    },
    AnalyzerBackend, GraphBackend, Node, Range, SolcRange, VarType,
};
use shared::{NodeIdx};

use solang_parser::pt::{Expression, Loc};

impl<T> TypesCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait TypesCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn types_call(&mut self, func_name: String, input_exprs: &[Expression], loc: Loc, ctx: ContextNode) -> Result<(), ExprErr> {
        match &*func_name {
            "type" => self.parse_ctx_expr(&input_exprs[0], ctx),
            "wrap" => {
                if input_exprs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(loc, format!("Expected a member type and an input to the wrap function, but got: {:?}", input_exprs)));
                }

                self.parse_inputs(ctx, loc, input_exprs)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) =
                        ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "ecrecover did not receive inputs".to_string(),
                        ));
                    };
                    input.expect_length(2).into_expr_err(loc)?;
                    let ret = input.as_vec();
                    let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                    let var = ContextVar::new_from_ty(
                        loc,
                        TyNode::from(wrapping_ty),
                        ctx,
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let to_be_wrapped = ret[1].expect_single().into_expr_err(loc)?;
                    let cvar =
                        ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                    let next = analyzer.advance_var_in_ctx(cvar, loc, ctx)?;
                    let expr = Elem::Expr(RangeExpr::new(
                        Elem::from(to_be_wrapped),
                        RangeOp::Cast,
                        Elem::from(cvar),
                    ));
                    next.set_range_min(analyzer, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, expr).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(cvar.into()), analyzer)
                        .into_expr_err(loc)
                })
            }
            "unwrap" => {
                self.parse_inputs(ctx, loc, input_exprs)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) =
                        ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                    else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "ecrecover did not receive inputs".to_string(),
                        ));
                    };
                    input.expect_length(2).into_expr_err(loc)?;
                    let ret = input.as_vec();
                    let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                    let mut var = ContextVar::new_from_builtin(
                        loc,
                        BuiltInNode::from(
                            TyNode::from(wrapping_ty)
                                .underlying(analyzer)
                                .into_expr_err(loc)?
                                .ty,
                        ),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let to_be_unwrapped = ret[1].expect_single().into_expr_err(loc)?;
                    var.display_name = format!(
                        "{}.unwrap({})",
                        TyNode::from(wrapping_ty)
                            .name(analyzer)
                            .into_expr_err(loc)?,
                        ContextVarNode::from(to_be_unwrapped)
                            .display_name(analyzer)
                            .into_expr_err(loc)?
                    );

                    let cvar =
                        ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                    cvar.set_range_min(analyzer, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    cvar.set_range_max(analyzer, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    let next = analyzer.advance_var_in_ctx(cvar, loc, ctx)?;
                    let expr = Elem::Expr(RangeExpr::new(
                        Elem::from(to_be_unwrapped),
                        RangeOp::Cast,
                        Elem::from(cvar),
                    ));
                    next.set_range_min(analyzer, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, expr).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(cvar.into()), analyzer)
                        .into_expr_err(loc)
                })
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin types function: \"{func_name}\", context: {}",
                    ctx.path(self),
                )
            ))
        }
    }

    fn cast(&mut self, ty: Builtin, func_idx: NodeIdx, input_exprs: &[Expression], loc: Loc, ctx: ContextNode) -> Result<(), ExprErr> {
        // it is a cast
        fn cast_match(
            ctx: ContextNode,
            loc: Loc,
            analyzer: &mut (impl GraphBackend + AnalyzerBackend),
            ty: &Builtin,
            ret: ExprRet,
            func_idx: NodeIdx,
        ) -> Result<(), ExprErr> {
            match ret {
                ExprRet::CtxKilled(kind) => {
                    ctx.kill(analyzer, loc, kind).into_expr_err(loc)
                }
                ExprRet::Null => Ok(()),
                ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                    let new_var = ContextVarNode::from(cvar)
                        .as_cast_tmp(loc, ctx, ty.clone(), analyzer)
                        .into_expr_err(loc)?;

                    new_var.underlying_mut(analyzer).into_expr_err(loc)?.ty =
                        VarType::try_from_idx(analyzer, func_idx).expect("");
                    // cast the ranges
                    if let Some(r) = ContextVarNode::from(cvar)
                        .range(analyzer)
                        .into_expr_err(loc)?
                    {
                        let curr_range =
                            SolcRange::try_from_builtin(ty).expect("No default range");
                        let mut min = r
                            .range_min()
                            .into_owned()
                            .cast(curr_range.range_min().into_owned());

                        min.cache_minimize(analyzer).into_expr_err(loc)?;
                        let mut max = r
                            .range_max()
                            .into_owned()
                            .cast(curr_range.range_max().into_owned());

                        max.cache_maximize(analyzer).into_expr_err(loc)?;

                        let existing_max =
                            r.evaled_range_max(analyzer).into_expr_err(loc)?;
                        // Check if the max value has changed once the cast is applied.
                        // If it hasnt, then the cast had no effect and we should adjust the naming
                        // to not muddle the CLI
                        if let Some(std::cmp::Ordering::Equal) = max
                            .maximize(analyzer)
                            .into_expr_err(loc)?
                            .range_ord(&existing_max)
                        {
                            // its a noop, reflect that in the naming
                            new_var.underlying_mut(analyzer).unwrap().display_name =
                                ContextVarNode::from(cvar)
                                    .display_name(analyzer)
                                    .into_expr_err(loc)?;
                        }

                        new_var.set_range_min(analyzer, min).into_expr_err(loc)?;
                        new_var.set_range_max(analyzer, max).into_expr_err(loc)?;
                        // cast the range exclusions - TODO: verify this is correct
                        let mut exclusions = r.range_exclusions();
                        exclusions.iter_mut().for_each(|range| {
                            *range =
                                range.clone().cast(curr_range.range_min().into_owned());
                        });
                        new_var
                            .set_range_exclusions(analyzer, exclusions)
                            .into_expr_err(loc)?;
                    }

                    ctx.push_expr(ExprRet::Single(new_var.into()), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| cast_match(ctx, loc, analyzer, ty, i, func_idx)),
            }
        }

        self.parse_ctx_expr(&input_exprs[0], ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Cast had no target type".to_string()));
            };

            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }

            cast_match(ctx, loc, analyzer, &ty, ret, func_idx)
        })
    }
}