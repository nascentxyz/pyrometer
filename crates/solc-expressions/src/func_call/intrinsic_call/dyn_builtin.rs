use crate::{ContextBuilder, ExprErr, IntoExprErr};

use graph::{
    nodes::{Builtin, Concrete, ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, Node, SolcRange, VarType,
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
                    analyzer.match_concat(ctx, loc, start.clone(), &inputs[1..], None)
                } else {
                    analyzer.match_concat(ctx, loc, start.clone(), &[], None)
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
        accum_node: Option<ContextVarNode>,
    ) -> Result<(), ExprErr> {
        if let Some(accum_node) = accum_node {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    self.concat_inner(loc, accum_node, ContextVarNode::from(var))?;
                    ctx.push_expr(ExprRet::Single(accum_node.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Null => {
                    ctx.push_expr(ExprRet::Single(accum_node.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, Some(accum_node))),
                ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            }
        } else {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    let acc = ContextVarNode::from(var)
                        .as_tmp(loc, ctx, self)
                        .into_expr_err(loc)?;
                    inputs
                        .iter()
                        .map(|i| self.match_concat(ctx, loc, i.clone(), inputs, Some(acc)))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    ctx.push_expr(ExprRet::Single(acc.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Null => Err(ExprErr::NoRhs(
                    loc,
                    "No input provided to concat function".to_string(),
                )),
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, None)),
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
                // TODO: improve length calculation here
                let min = r.min.clone().concat(r2.min.clone());
                let max = r.max.clone().concat(r2.max.clone());
                accum.set_range_min(self, min).into_expr_err(loc)?;
                accum.set_range_max(self, max).into_expr_err(loc)?;
                Ok(())
            }
            (_, _) => Ok(()),
        }
    }
}
