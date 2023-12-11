use crate::{array::Array, ContextBuilder, ExprErr, IntoExprErr, ListAccess};

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend,
};

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> ArrayCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
pub trait ArrayCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn array_call(
        &mut self,
        func_name: String,
        input_exprs: &[Expression],
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "push" => {
                if input_exprs.len() == 1 {
                    // array.push() is valid syntax. It pushes a new
                    // empty element onto the expr ret stack
                    self.parse_ctx_expr(&input_exprs[0], ctx)?;
                    self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "array[].push(..) was not an array to push to".to_string(),
                            ));
                        };

                        let arr = array.expect_single().into_expr_err(loc)?;
                        let arr = ContextVarNode::from(arr).latest_version(analyzer);
                        // get length
                        let len = analyzer.tmp_length(arr, ctx, loc);

                        let len_as_idx = len.as_tmp(loc, ctx, analyzer).into_expr_err(loc)?;
                        // set length as index
                        analyzer.index_into_array_inner(
                            ctx,
                            loc,
                            ExprRet::Single(arr.latest_version(analyzer).into()),
                            ExprRet::Single(len_as_idx.latest_version(analyzer).into()),
                        )?;
                        Ok(())
                    })
                } else if input_exprs.len() == 2 {
                    // array.push(value)
                    self.parse_ctx_expr(&input_exprs[0], ctx)?;
                    self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                        let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoLhs(
                                loc,
                                "array[].push(..) was not an array to push to".to_string(),
                            ));
                        };
                        if matches!(array, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        analyzer.parse_ctx_expr(&input_exprs[1], ctx)?;
                        analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                            let Some(new_elem) =
                                ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                            else {
                                return Err(ExprErr::NoRhs(
                                    loc,
                                    "array[].push(..) was not given an element to push".to_string(),
                                ));
                            };

                            if matches!(new_elem, ExprRet::CtxKilled(_)) {
                                ctx.push_expr(new_elem, analyzer).into_expr_err(loc)?;
                                return Ok(());
                            }

                            let arr = array.expect_single().into_expr_err(loc)?;
                            let arr = ContextVarNode::from(arr).latest_version(analyzer);
                            // get length
                            let len = analyzer.tmp_length(arr, ctx, loc);

                            let len_as_idx = len.as_tmp(loc, ctx, analyzer).into_expr_err(loc)?;
                            // set length as index
                            analyzer.index_into_array_inner(
                                ctx,
                                loc,
                                ExprRet::Single(arr.latest_version(analyzer).into()),
                                ExprRet::Single(len_as_idx.latest_version(analyzer).into()),
                            )?;
                            let index = ctx
                                .pop_expr_latest(loc, analyzer)
                                .into_expr_err(loc)?
                                .unwrap();
                            if matches!(index, ExprRet::CtxKilled(_)) {
                                ctx.push_expr(index, analyzer).into_expr_err(loc)?;
                                return Ok(());
                            }
                            // assign index to new_elem
                            analyzer.match_assign_sides(ctx, loc, &index, &new_elem)
                        })
                    })
                } else {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "array[].push(..) expected 0 or 1 inputs, got: {}",
                            input_exprs.len()
                        ),
                    ));
                }
            }
            "pop" => {
                if input_exprs.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "array[].pop() expected 0 inputs, got: {}",
                            input_exprs.len()
                        ),
                    ));
                }
                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "array[].pop() was not an array to pop from".to_string(),
                        ));
                    };
                    if matches!(array, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    // get the array
                    let arr = array.expect_single().into_expr_err(loc)?;
                    let arr = ContextVarNode::from(arr).latest_version(analyzer);

                    // get length
                    analyzer.match_length(ctx, loc, array, false)?;
                    let Some(len) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(
                            loc,
                            "array[].pop() was not an array to pop from".to_string(),
                        ));
                    };
                    let len = len.expect_single().into_expr_err(loc)?;
                    let next_len = analyzer.advance_var_in_ctx(len.into(), loc, ctx)?;
                    next_len
                        .set_range_min(
                            analyzer,
                            Elem::from(len) - Elem::from(Concrete::from(U256::from(1))),
                        )
                        .into_expr_err(loc)?;
                    next_len
                        .set_range_max(
                            analyzer,
                            Elem::from(len) - Elem::from(Concrete::from(U256::from(1))),
                        )
                        .into_expr_err(loc)?;

                    // set length as index
                    analyzer.index_into_array_inner(
                        ctx,
                        loc,
                        ExprRet::Single(arr.latest_version(analyzer).into()),
                        ExprRet::Single(next_len.latest_version(analyzer).into()),
                    )
                })
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin array function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
