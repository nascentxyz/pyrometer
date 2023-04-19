use crate::context::ExprErr;
use crate::{
    context::{
        exprs::MemberAccess, func_call::intrinsic_call::IntrinsicFuncCaller, func_call::FuncCaller,
        ContextBuilder,
    },
    ExprRet,
};
use shared::NodeIdx;

use shared::context::ContextVarNode;

use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::ContextNode,
    nodes::*,
};
use solang_parser::pt::{Expression, Identifier, Loc, NamedArgument};

impl<T> NameSpaceFuncCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
}
pub trait NameSpaceFuncCaller:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
    #[tracing::instrument(level = "trace", skip_all)]
    fn call_name_spaced_named_func(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        member_expr: &Expression,
        _ident: &Identifier,
        _input_args: &[NamedArgument],
    ) -> Result<ExprRet, ExprErr> {
        let (_mem_ctx, _member) = self.parse_ctx_expr(member_expr, ctx)?.expect_single(*loc)?;

        todo!("here");
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn call_name_spaced_func(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &[Expression],
    ) -> Result<ExprRet, ExprErr> {
        use solang_parser::pt::Expression::*;

        if let Variable(Identifier { name, .. }) = member_expr {
            if name == "abi" {
                let func_name = format!("abi.{}", ident.name);
                let as_fn = self
                    .builtin_fns()
                    .get(&func_name)
                    .unwrap_or_else(|| panic!("No builtin function with name {func_name}"));
                let fn_node = FunctionNode::from(self.add_node(as_fn.clone()));
                return self.intrinsic_func_call(loc, input_exprs, fn_node.into(), ctx);
            }
        }

        let ret = self.parse_ctx_expr(member_expr, ctx)?;
        self.match_namespaced_member(ctx, *loc, member_expr, ident, input_exprs, ret)
    }

    fn match_namespaced_member(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &[Expression],
        ret: ExprRet,
    ) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => {
                self.call_name_spaced_func_inner(ctx, loc, member_expr, ident, input_exprs, inner)
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|ret| {
                        self.match_namespaced_member(ctx, loc, member_expr, ident, input_exprs, ret)
                    })
                    .collect::<Result<Vec<_>, ExprErr>>()?,
            )),
            ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                Box::new(self.match_namespaced_member(
                    ctx,
                    loc,
                    member_expr,
                    ident,
                    input_exprs,
                    *w1,
                )?),
                Box::new(self.match_namespaced_member(
                    ctx,
                    loc,
                    member_expr,
                    ident,
                    input_exprs,
                    *w2,
                )?),
            )),
            ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
        }
    }

    fn call_name_spaced_func_inner(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &[Expression],
        (mem_ctx, member): (ContextNode, NodeIdx),
    ) -> Result<ExprRet, ExprErr> {
        use solang_parser::pt::Expression::*;
        tracing::trace!(
            "namespaced function call: {:?}.{:?}(..)",
            ContextVarNode::from(member).display_name(self),
            ident.name
        );

        let funcs = self.visible_member_funcs(ctx, member);
        // filter down all funcs to those that match
        let possible_funcs = funcs
            .iter()
            .filter(|func| {
                func.name(self)
                    .unwrap()
                    .starts_with(&format!("{}(", ident.name))
            })
            .copied()
            .collect::<Vec<_>>();

        let mut inputs = vec![ExprRet::Single((mem_ctx, member))];
        inputs.extend(
            input_exprs
                .iter()
                .map(|expr| self.parse_ctx_expr(expr, ctx))
                .collect::<Result<Vec<_>, ExprErr>>()?,
        );

        if possible_funcs.is_empty() {
            let inputs = ExprRet::Multi(inputs);
            if inputs.has_killed() {
                return Ok(ExprRet::CtxKilled);
            }
            let as_input_str = inputs.try_as_func_input_str(self);

            let expr = &MemberAccess(
                loc,
                Box::new(member_expr.clone()),
                Identifier {
                    loc: ident.loc,
                    name: format!("{}{}", ident.name, as_input_str),
                },
            );
            let ret = self.parse_ctx_expr(expr, ctx)?;
            let mut modifier_input_exprs = vec![member_expr.clone()];
            modifier_input_exprs.extend(input_exprs.to_vec());
            self.match_intrinsic_fallback(&loc, &modifier_input_exprs, ret)
        } else if possible_funcs.len() == 1 {
            let func = possible_funcs[0];
            if func.params(self).len() < inputs.len() {
                inputs = inputs[1..].to_vec();
            }
            let inputs = ExprRet::Multi(inputs);
            if inputs.has_killed() {
                return Ok(ExprRet::CtxKilled);
            }
            self.setup_fn_call(&ident.loc, &inputs, func.into(), ctx, None)
        } else {
            // this is the annoying case due to function overloading & type inference on number literals
            let mut lits = vec![false];
            lits.extend(
                input_exprs
                    .iter()
                    .map(|expr| {
                        match expr {
                            Negate(_, expr) => {
                                // negative number potentially
                                matches!(**expr, NumberLiteral(..) | HexLiteral(..))
                            }
                            NumberLiteral(..) | HexLiteral(..) => true,
                            _ => false,
                        }
                    })
                    .collect::<Vec<bool>>(),
            );

            let inputs = ExprRet::Multi(inputs);
            if inputs.has_killed() {
                return Ok(ExprRet::CtxKilled);
            }
            if let Some(func) =
                self.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
            {
                self.setup_fn_call(&loc, &inputs, func.into(), ctx, None)
            } else {
                Err(ExprErr::FunctionNotFound(
                    loc,
                    "Could not find function".to_string(),
                ))
            }
        }
    }
}
