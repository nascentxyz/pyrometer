use crate::{
    context::{
        exprs::MemberAccess, func_call::intrinsic_call::IntrinsicFuncCaller, func_call::FuncCaller,
        ContextBuilder,
    },
    ExprRet,
};

use shared::context::ContextVarNode;

use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::ContextNode,
    nodes::*,
};
use solang_parser::pt::{Expression, Identifier, Loc, NamedArgument};

impl<T> NameSpaceFuncCaller for T where T: AnalyzerLike<Expr = Expression> + Sized + GraphLike {}
pub trait NameSpaceFuncCaller: AnalyzerLike<Expr = Expression> + Sized + GraphLike {
    #[tracing::instrument(level = "trace", skip_all)]
    fn call_name_spaced_named_func(
        &mut self,
        ctx: ContextNode,
        _loc: &Loc,
        member_expr: &Expression,
        _ident: &Identifier,
        _input_args: &[NamedArgument],
    ) -> ExprRet {
        let (_mem_ctx, _member) = self.parse_ctx_expr(member_expr, ctx).expect_single();

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
    ) -> ExprRet {
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

        let (mem_ctx, member) = self.parse_ctx_expr(member_expr, ctx).expect_single();
        tracing::trace!(
            "namespaced function call: {:?}.{:?}(..)",
            ContextVarNode::from(member).display_name(self),
            ident.name
        );

        let funcs = self.visible_member_funcs(ctx, member);
        // filter down all funcs to those that match
        let possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).starts_with(&format!("{}(", ident.name)))
            .copied()
            .collect::<Vec<_>>();

        let mut inputs = vec![ExprRet::Single((mem_ctx, member))];
        inputs.extend(
            input_exprs
                .iter()
                .map(|expr| self.parse_ctx_expr(expr, ctx))
                .collect::<Vec<_>>(),
        );

        if possible_funcs.is_empty() {
            let as_input_str = ExprRet::Multi(inputs).try_as_func_input_str(self);
            let (func_ctx, func_idx) = match self
                .parse_ctx_expr(
                    &MemberAccess(
                        *loc,
                        Box::new(member_expr.clone()),
                        Identifier {
                            loc: ident.loc,
                            name: format!("{}{}", ident.name, as_input_str),
                        },
                    ),
                    ctx,
                )
                .flatten()
            {
                ExprRet::Single((ctx, idx)) => (ctx, idx),
                m @ ExprRet::Multi(_) => m.expect_single(),
                ExprRet::CtxKilled => return ExprRet::CtxKilled,
                e => todo!("got fork in func call: {:?}", e),
            };
            let mut modifierd_input_exprs = vec![member_expr.clone()];
            modifierd_input_exprs.extend(input_exprs.to_vec());
            self.intrinsic_func_call(loc, &modifierd_input_exprs, func_idx, func_ctx)
        } else if possible_funcs.len() == 1 {
            let func = possible_funcs[0];
            if func.params(self).len() < inputs.len() {
                inputs = inputs[1..].to_vec();
            }
            self.setup_fn_call(&ident.loc, &ExprRet::Multi(inputs), func.into(), ctx, None)
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
            if let Some(func) =
                self.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
            {
                self.setup_fn_call(loc, &inputs, func.into(), ctx, None)
            } else {
                ExprRet::CtxKilled
            }
        }
    }
}
