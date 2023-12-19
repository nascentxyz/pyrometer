use crate::{
    variable::Variable, ContextBuilder, ExprErr, ExpressionParser, IntoExprErr, ListAccess,
};

use graph::{
    elem::RangeElem,
    nodes::{Builtin, Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, SolcRange, VarType,
};

use solang_parser::pt::{Expression, Loc};

impl<T> DynBuiltinCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{}

/// Trait for calling dynamic builtin-based intrinsic functions, like `concat`
pub trait DynBuiltinCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a dynamic builtin type's builtin function call
    fn dyn_builtin_call(
        &mut self,
        func_name: String,
        input_exprs: &[Expression],
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "concat" => self.concat(&loc, input_exprs, ctx),
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin dynamic builtin function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Concatenate two dynamic builtins
    fn concat(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        input_exprs[1..].iter().try_for_each(|expr| {
            self.parse_ctx_expr(expr, ctx)?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let input = ctx
                    .pop_expr_latest(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or(ExprRet::Null);
                ctx.append_tmp_expr(input, analyzer).into_expr_err(loc)
            })
        })?;

        self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
            let Some(inputs) = ctx.pop_tmp_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Concatenation failed".to_string()));
            };
            if matches!(inputs, ExprRet::CtxKilled(_)) {
                ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            let inputs = inputs.as_vec();
            if inputs.is_empty() {
                ctx.push_expr(ExprRet::Multi(vec![]), analyzer)
                    .into_expr_err(loc)?;
                Ok(())
            } else {
                let start = &inputs[0];
                if inputs.len() > 1 {
                    analyzer.match_concat(ctx, loc, start.clone(), &inputs[1..], false)
                } else {
                    analyzer.match_concat(ctx, loc, start.clone(), &[], false)
                }
            }
        })
    }

    /// Match on the expression returns
    fn match_concat(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        curr: ExprRet,
        inputs: &[ExprRet],
        has_accum_node: bool,
    ) -> Result<(), ExprErr> {
        if has_accum_node {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    // pop the accumulation node off the stack
                    let accum_node = ctx
                        .pop_expr_latest(loc, self)
                        .into_expr_err(loc)?
                        .unwrap()
                        .expect_single()
                        .unwrap();

                    let accum_node = self.advance_var_in_ctx(accum_node.into(), loc, ctx)?;
                    let name = accum_node.display_name(self).into_expr_err(loc)?;
                    let next_var = ContextVarNode::from(var);
                    let next_name = next_var.display_name(self).into_expr_err(loc)?;
                    accum_node
                        .underlying_mut(self)
                        .into_expr_err(loc)?
                        .display_name = format!("concat({name}, {next_name})");

                    // concat into it
                    self.concat_inner(loc, accum_node, next_var)?;

                    // add it back to the stack
                    ctx.push_expr(ExprRet::Single(accum_node.into()), self)
                        .into_expr_err(loc)?;

                    Ok(())
                }
                ExprRet::Null => Ok(()),
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, true)),
                ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            }
        } else {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    let acc = ContextVarNode::from(var)
                        .as_tmp(loc, ctx, self)
                        .into_expr_err(loc)?;
                    self.add_edge(acc.0, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(acc, self).into_expr_err(loc)?;

                    ctx.push_expr(ExprRet::Single(acc.into()), self)
                        .into_expr_err(loc)?;

                    inputs
                        .iter()
                        .map(|i| self.match_concat(ctx, loc, i.clone(), inputs, true))
                        .collect::<Result<Vec<_>, ExprErr>>()?;

                    // create the length variable
                    let _ = self.tmp_length(acc.latest_version(self), ctx, loc);

                    Ok(())
                }
                ExprRet::Null => Err(ExprErr::NoRhs(
                    loc,
                    "No input provided to concat function".to_string(),
                )),
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, false)),
                ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            }
        }
    }

    /// Perform the concatenation
    fn concat_inner(
        &mut self,
        loc: Loc,
        accum: ContextVarNode,
        right: ContextVarNode,
    ) -> Result<(), ExprErr> {
        match (
            accum.ty(self).into_expr_err(loc)?,
            right.ty(self).into_expr_err(loc)?,
        ) {
            (VarType::Concrete(accum_cnode), VarType::Concrete(right_cnode)) => {
                let new_ty = match (
                    accum_cnode.underlying(self).into_expr_err(loc)?,
                    right_cnode.underlying(self).into_expr_err(loc)?,
                ) {
                    (accum_node @ Concrete::String(..), right_node @ Concrete::String(..)) => {
                        let new_val = accum_node.clone().concat(right_node).unwrap();
                        let new_cnode = self.add_node(Node::Concrete(new_val));
                        VarType::Concrete(new_cnode.into())
                    }
                    (accum_node @ Concrete::DynBytes(..), right_node @ Concrete::DynBytes(..)) => {
                        let new_val = accum_node.clone().concat(right_node).unwrap();
                        let new_cnode = self.add_node(Node::Concrete(new_val));
                        VarType::Concrete(new_cnode.into())
                    }
                    (a, b) => {
                        // Invalid solidity
                        return Err(ExprErr::InvalidFunctionInput(loc, format!("Type mismatch: {a:?} for left hand side and type: {b:?} for right hand side")));
                    }
                };
                accum.underlying_mut(self).into_expr_err(loc)?.ty = new_ty;
                Ok(())
            }
            (VarType::Concrete(accum_cnode), VarType::BuiltIn(_bn, Some(r2))) => {
                let underlying = accum_cnode.underlying(self).into_expr_err(loc)?;
                // let val = match underlying {
                //     Concrete::String(val) => {
                //         val
                //             .chars()
                //             .enumerate()
                //             .map(|(i, v)| {
                //                 let idx = Elem::from(Concrete::from(U256::from(i)));
                //                 let mut bytes = [0x00; 32];
                //                 v.encode_utf8(&mut bytes[..]);
                //                 let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                //                 (idx, v)
                //             })
                //             .collect::<BTreeMap<_, _>>()
                //     }
                //     Concrete::DynBytes(val) => {
                //         val
                //             .iter()
                //             .enumerate()
                //             .map(|(i, v)| {
                //                 let idx = Elem::from(Concrete::from(U256::from(i)));
                //                 let mut bytes = [0x00; 32];
                //                 bytes[0] = *v;
                //                 let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                //                 (idx, v)
                //             })
                //             .collect::<BTreeMap<_, _>>()
                //     }
                //     b => return Err(ExprErr::InvalidFunctionInput(loc, format!("Type mismatch: expected String or Bytes for concat input but found: {b:?}")))
                // };
                // TODO: Extend with bn

                let range = SolcRange::from(underlying.clone()).unwrap();
                let min = range.min.clone().concat(r2.min.clone());
                let max = range.max.clone().concat(r2.max.clone());
                accum.set_range_min(self, min).into_expr_err(loc)?;
                accum.set_range_max(self, max).into_expr_err(loc)?;

                let new_ty =
                    VarType::BuiltIn(self.builtin_or_add(Builtin::String).into(), Some(range));
                accum.underlying_mut(self).into_expr_err(loc)?.ty = new_ty;
                Ok(())
            }
            (VarType::BuiltIn(_bn, Some(r)), VarType::BuiltIn(_bn2, Some(r2))) => {
                let min = r
                    .min
                    .clone()
                    .concat(r2.min.clone())
                    .simplify_minimize(&mut Default::default(), self)
                    .into_expr_err(loc)?;
                let max = r
                    .max
                    .clone()
                    .concat(r2.max.clone())
                    .simplify_maximize(&mut Default::default(), self)
                    .into_expr_err(loc)?;
                accum.set_range_min(self, min).into_expr_err(loc)?;
                accum.set_range_max(self, max).into_expr_err(loc)?;
                Ok(())
            }
            (_, _) => Ok(()),
        }
    }
}
