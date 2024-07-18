use crate::assign::Assign;
use crate::func_caller::NamedOrUnnamedArgs;
use crate::{array::Array, bin_op::BinOp, ContextBuilder, ExpressionParser, ListAccess};

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, Node,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> ArrayCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling array-based intrinsic functions
pub trait ArrayCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform an `array.<..>` function call
    fn array_call_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match func_name {
            "push" => {
                let inputs_vec = inputs.as_vec();
                let arr = inputs_vec[0].expect_single().into_expr_err(loc)?;
                let arr = ContextVarNode::from(arr).latest_version(self);

                // get length
                let len = self
                    .get_length(arena, ctx, arr, true, loc)?
                    .unwrap()
                    .latest_version(self);

                // get the index access for the *previous* length
                let index_access = self
                    .index_into_array_raw(arena, ctx, loc, len, arr, false, true)?
                    .unwrap();

                // create a temporary 1 variable
                let tmp_one = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;

                // add 1 to the length
                let tmp_len = self.op(arena, loc, len, tmp_one, ctx, RangeOp::Add(false), false)?;

                let tmp_len = ContextVarNode::from(tmp_len.expect_single().unwrap());
                tmp_len.underlying_mut(self).unwrap().is_tmp = false;

                // set the new length
                self.set_var_as_length(arena, ctx, loc, tmp_len, arr.latest_version(self))?;

                if let Some(push_elem) = inputs_vec.get(1) {
                    self.match_assign_sides(
                        arena,
                        ctx,
                        loc,
                        &ExprRet::Single(index_access.0.into()),
                        push_elem,
                    )
                } else {
                    ctx.push_expr(ExprRet::Single(index_access.0.into()), self)
                        .into_expr_err(loc)
                }
            }
            "pop" => {
                todo!();
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

    /// Perform an `array.<..>` function call
    fn array_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_name: String,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "push" => {
                if input_exprs.len() == 1 {
                    // array.push() is valid syntax. It pushes a new
                    // empty element onto the expr ret stack
                    self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
                    self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoRhs(
                                loc,
                                "array[].push(..) was not given an element to push".to_string(),
                            ));
                        };

                        if matches!(array, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        // get length
                        let arr = array.expect_single().into_expr_err(loc)?;
                        let arr = ContextVarNode::from(arr).latest_version(analyzer);

                        // get length
                        let len = analyzer
                            .get_length(arena, ctx, arr, true, loc)?
                            .unwrap()
                            .latest_version(analyzer);

                        // get the index access and add it to the stack
                        let _ = analyzer
                            .index_into_array_raw(arena, ctx, loc, len, arr, false, false)?;

                        // create a temporary 1 variable
                        let cnode =
                            analyzer.add_node(Node::Concrete(Concrete::from(U256::from(1))));
                        let tmp_one = Node::ContextVar(
                            ContextVar::new_from_concrete(
                                Loc::Implicit,
                                ctx,
                                cnode.into(),
                                analyzer,
                            )
                            .into_expr_err(loc)?,
                        );
                        let one = ContextVarNode::from(analyzer.add_node(tmp_one));

                        // add 1 to the length
                        let tmp_len =
                            analyzer.op(arena, loc, len, one, ctx, RangeOp::Add(false), false)?;

                        let tmp_len = ContextVarNode::from(tmp_len.expect_single().unwrap());
                        tmp_len.underlying_mut(analyzer).unwrap().is_tmp = false;

                        analyzer.set_var_as_length(
                            arena,
                            ctx,
                            loc,
                            tmp_len,
                            arr.latest_version(analyzer),
                        )?;

                        Ok(())
                    })
                } else if input_exprs.len() == 2 {
                    // array.push(value)
                    self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
                    self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
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
                        analyzer.parse_ctx_expr(
                            arena,
                            &input_exprs.unnamed_args().unwrap()[1],
                            ctx,
                        )?;
                        analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
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
                            let pushed_value =
                                ContextVarNode::from(new_elem.expect_single().unwrap());

                            // get length
                            let arr = array.expect_single().into_expr_err(loc)?;
                            let arr = ContextVarNode::from(arr).latest_version(analyzer);

                            // get length
                            let len = analyzer
                                .get_length(arena, ctx, arr, true, loc)?
                                .unwrap()
                                .latest_version(analyzer);

                            // get the index access for the *previous* length
                            let index_access = analyzer
                                .index_into_array_raw(arena, ctx, loc, len, arr, false, true)?
                                .unwrap();
                            // create a temporary 1 variable
                            let cnode =
                                analyzer.add_node(Node::Concrete(Concrete::from(U256::from(1))));
                            let tmp_one = Node::ContextVar(
                                ContextVar::new_from_concrete(
                                    Loc::Implicit,
                                    ctx,
                                    cnode.into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?,
                            );
                            let one = ContextVarNode::from(analyzer.add_node(tmp_one));

                            // add 1 to the length
                            let tmp_len = analyzer.op(
                                arena,
                                loc,
                                len,
                                one,
                                ctx,
                                RangeOp::Add(false),
                                false,
                            )?;

                            let tmp_len = ContextVarNode::from(tmp_len.expect_single().unwrap());
                            tmp_len.underlying_mut(analyzer).unwrap().is_tmp = false;

                            // set the new length
                            analyzer.set_var_as_length(
                                arena,
                                ctx,
                                loc,
                                tmp_len,
                                arr.latest_version(analyzer),
                            )?;

                            // update the index access's range
                            let elem = Elem::from(pushed_value);
                            index_access
                                .set_range_min(analyzer, arena, elem.clone())
                                .into_expr_err(loc)?;
                            index_access
                                .set_range_max(analyzer, arena, elem.clone())
                                .into_expr_err(loc)?;

                            // update the array using the index access
                            analyzer.update_array_from_index_access(
                                arena,
                                ctx,
                                loc,
                                len,
                                index_access.latest_version(analyzer),
                                arr.latest_version(analyzer),
                            )
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
                self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
                self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
                    let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "array[].pop() was not given an array".to_string(),
                        ));
                    };

                    if matches!(array, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    // get length
                    let arr = array.expect_single().into_expr_err(loc)?;
                    let arr = ContextVarNode::from(arr).latest_version(analyzer);

                    // get length
                    let len = analyzer
                        .get_length(arena, ctx, arr, true, loc)?
                        .unwrap()
                        .latest_version(analyzer);

                    // create a temporary 1 variable
                    let cnode = analyzer.add_node(Node::Concrete(Concrete::from(U256::from(1))));
                    let tmp_one = Node::ContextVar(
                        ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode.into(), analyzer)
                            .into_expr_err(loc)?,
                    );
                    let one = ContextVarNode::from(analyzer.add_node(tmp_one));

                    // subtract 1 from the length
                    let tmp_len =
                        analyzer.op(arena, loc, len, one, ctx, RangeOp::Sub(false), false)?;

                    let tmp_len = ContextVarNode::from(tmp_len.expect_single().unwrap());
                    tmp_len.underlying_mut(analyzer).unwrap().is_tmp = false;

                    // get the index access
                    let index_access = analyzer
                        .index_into_array_raw(arena, ctx, loc, tmp_len, arr, false, true)?
                        .unwrap();

                    analyzer.set_var_as_length(
                        arena,
                        ctx,
                        loc,
                        tmp_len,
                        arr.latest_version(analyzer),
                    )?;
                    index_access
                        .set_range_min(analyzer, arena, Elem::Null)
                        .into_expr_err(loc)?;
                    index_access
                        .set_range_max(analyzer, arena, Elem::Null)
                        .into_expr_err(loc)?;

                    analyzer.update_array_from_index_access(
                        arena,
                        ctx,
                        loc,
                        tmp_len,
                        index_access.latest_version(analyzer),
                        arr.latest_version(analyzer),
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
