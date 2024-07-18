use crate::assign::Assign;
use crate::{array::Array, bin_op::BinOp, ListAccess};

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> ArrayCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling array-based intrinsic functions
pub trait ArrayCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform an `array.<..>` function call
    #[tracing::instrument(level = "trace", skip_all)]
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
                if inputs.len() != 1 {
                    return Err(ExprErr::InvalidFunctionInput(
                        loc,
                        format!(
                            "array[].pop() expected 0 inputs, got: {}",
                            inputs.len().saturating_sub(1)
                        ),
                    ));
                }

                let [arr] = inputs.into_sized();
                let arr = ContextVarNode::from(arr.expect_single().into_expr_err(loc)?)
                    .latest_version(self);

                // get length
                let len = self
                    .get_length(arena, ctx, arr, true, loc)?
                    .unwrap()
                    .latest_version(self);

                // create a temporary 1 variable
                let one = self.add_concrete_var(ctx, Concrete::from(U256::from(1)), loc)?;

                // subtract 1 from the length
                let tmp_len = self.op(arena, loc, len, one, ctx, RangeOp::Sub(false), false)?;

                let tmp_len = ContextVarNode::from(tmp_len.expect_single().unwrap());
                tmp_len.underlying_mut(self).unwrap().is_tmp = false;

                // get the index access
                let index_access = self
                    .index_into_array_raw(arena, ctx, loc, tmp_len, arr, false, true)?
                    .unwrap();

                self.set_var_as_length(arena, ctx, loc, tmp_len, arr.latest_version(self))?;
                index_access
                    .set_range_min(self, arena, Elem::Null)
                    .into_expr_err(loc)?;
                index_access
                    .set_range_max(self, arena, Elem::Null)
                    .into_expr_err(loc)?;

                self.update_array_from_index_access(
                    arena,
                    ctx,
                    loc,
                    tmp_len,
                    index_access.latest_version(self),
                    arr.latest_version(self),
                )
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
