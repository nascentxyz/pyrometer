use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::context::{
    exprs::MemberAccess, func_call::intrinsic_call::IntrinsicFuncCaller, func_call::FuncCaller,
    ContextBuilder,
};
use shared::context::ExprRet;
use shared::NodeIdx;

use shared::context::ContextVarNode;

use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::ContextNode,
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
        _loc: &Loc,
        member_expr: &Expression,
        _ident: &Identifier,
        _input_args: &[NamedArgument],
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(member_expr, ctx)?;
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
    ) -> Result<(), ExprErr> {
        use solang_parser::pt::Expression::*;

        if let Variable(Identifier { name, .. }) = member_expr {
            if name == "abi" {
                let func_name = format!("abi.{}", ident.name);
                let fn_node = self
                    .builtin_fn_or_maybe_add(&func_name)
                    .unwrap_or_else(|| panic!("No builtin function with name {func_name}"));
                return self.intrinsic_func_call(loc, input_exprs, fn_node, ctx);
            }
        }

        self.parse_ctx_expr(member_expr, ctx)?;
        self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "Namespace function call had no namespace".to_string()))
            };
            analyzer.match_namespaced_member(ctx, loc, member_expr, ident, input_exprs, ret)
        })
    }

    fn match_namespaced_member(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &[Expression],
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => {
                self.call_name_spaced_func_inner(ctx, loc, member_expr, ident, input_exprs, inner)
            }
            ExprRet::Multi(inner) => inner.into_iter().try_for_each(|ret| {
                self.match_namespaced_member(ctx, loc, member_expr, ident, input_exprs, ret)
            }),
            ExprRet::CtxKilled => {
                ctx.push_expr(ExprRet::CtxKilled, self).into_expr_err(loc)?;
                Ok(())
            }
        }
    }

    fn call_name_spaced_func_inner(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &[Expression],
        member: NodeIdx,
    ) -> Result<(), ExprErr> {
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

        ctx.push_expr(ExprRet::Single(member), self)
            .into_expr_err(loc)?;
        self.parse_inputs(ctx, loc, input_exprs)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(inputs) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "Namespace function call had no inputs".to_string()))
            };
            if possible_funcs.is_empty() {
                if inputs.has_killed() {
                    ctx.push_expr(ExprRet::CtxKilled, analyzer).into_expr_err(loc)?;
                    return Ok(())
                }
                let as_input_str = inputs.try_as_func_input_str(analyzer);

                let expr = &MemberAccess(
                    loc,
                    Box::new(member_expr.clone()),
                    Identifier {
                        loc: ident.loc,
                        name: format!("{}{}", ident.name, as_input_str),
                    },
                );
                analyzer.parse_ctx_expr(expr, ctx)?;
                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoLhs(loc, "Fallback function parse failure".to_string()))
                    };
                    let mut modifier_input_exprs = vec![member_expr.clone()];
                    modifier_input_exprs.extend(input_exprs.to_vec());
                    analyzer.match_intrinsic_fallback(ctx, &loc, &modifier_input_exprs, ret)
                })
            } else if possible_funcs.len() == 1 {
                let mut inputs = inputs.as_vec();
                let func = possible_funcs[0];
                if func.params(analyzer).len() < inputs.len() {
                    inputs = inputs[1..].to_vec();
                }
                let inputs = ExprRet::Multi(inputs);
                if inputs.has_killed() {
                    ctx.push_expr(ExprRet::CtxKilled, analyzer).into_expr_err(loc)?;
                    return Ok(())
                }

                analyzer.setup_fn_call(&ident.loc, &inputs, func.into(), ctx, None)
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

                if inputs.has_killed() {
                    ctx.push_expr(ExprRet::CtxKilled, analyzer).into_expr_err(loc)?;
                    return Ok(())
                }
                if let Some(func) =
                    analyzer.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
                {
                    analyzer.setup_fn_call(&loc, &inputs, func.into(), ctx, None)
                } else {
                    Err(ExprErr::FunctionNotFound(
                        loc,
                        "Could not find function".to_string(),
                    ))
                }
            }
        })
    }
}
