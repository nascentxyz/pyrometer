use crate::{
	ExprRet,
	context::{
		func_call::intrinsic_call::IntrinsicFuncCaller,
		exprs::MemberAccess,
		func_call::FuncCaller,
		ContextBuilder
	}
};

use shared::context::ContextVarNode;


use solang_parser::pt::{Loc, Identifier, Expression, NamedArgument};
use shared::{context::ContextNode, analyzer::{AnalyzerLike, GraphLike}, nodes::*, Node};

impl<T> NameSpaceFuncCaller for T where T: AnalyzerLike<Expr = Expression> + Sized + GraphLike  {}
pub trait NameSpaceFuncCaller: AnalyzerLike<Expr = Expression> + Sized + GraphLike  {
	fn call_name_spaced_named_func(
		&mut self,
		ctx: ContextNode,
        loc: &Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_args: &[NamedArgument],
    ) -> ExprRet {
        let (mem_ctx, member) = self.parse_ctx_expr(member_expr, ctx).expect_single();

        todo!("here");
    }

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

        let inputs = match ContextVarNode::from(member).underlying(self).ty {
            VarType::User(TypeNode::Contract(_), _) => input_exprs
                .iter()
                .map(|expr| self.parse_ctx_expr(expr, ctx))
                .collect::<Vec<_>>(),
            _ => {
                let mut inputs = vec![ExprRet::Single((mem_ctx, member))];
                inputs.extend(
                    input_exprs
                        .iter()
                        .map(|expr| self.parse_ctx_expr(expr, ctx))
                        .collect::<Vec<_>>(),
                );
                inputs
            }
        };

        let inputs = ExprRet::Multi(inputs);
        let func_str = format!(
            "{}.{}({})",
            ContextVarNode::from(member).display_name(self),
            ident,
            inputs
                .as_flat_vec()
                .iter()
                .map(|cnode| ContextVarNode::from(*cnode).display_name(self))
                .collect::<Vec<_>>()
                .join(", ")
        );
        if !inputs.has_literal() {
            // TODO: handle implicit upcast
            let as_input_str = inputs.try_as_func_input_str(self);

            let (_func_ctx, func_idx) = match self.parse_ctx_expr(
                &MemberAccess(
                    *loc,
                    Box::new(member_expr.clone()),
                    Identifier {
                        loc: ident.loc,
                        name: format!("{}{}", ident.name, as_input_str),
                    },
                ),
                ctx,
            ) {
                ExprRet::Single((ctx, idx)) => (ctx, idx),
                m @ ExprRet::Multi(_) => m.expect_single(),
                ExprRet::CtxKilled => return ExprRet::CtxKilled,
                e => todo!("got fork in func call: {:?}", e),
            };

            if matches!(self.node(func_idx), Node::Function(..)) {
                // intrinsic
                let mut inputs: Vec<Expression> = vec![member_expr.clone()];
                inputs.extend(input_exprs.to_vec());
                self.intrinsic_func_call(loc, &inputs, func_idx, ctx)
            } else {
                self.func_call(
                    ctx,
                    *loc,
                    &inputs,
                    ContextVarNode::from(func_idx)
                        .ty(self)
                        .func_node(self)
                        .unwrap_or_else(|| panic!("expected a function node, was: {:?}", self.node(func_idx))),
                    Some(func_str),
                )
            }
        } else {
            // we need to disambiguate the literals
            let ty = &ContextVarNode::from(member).underlying(self).ty;
            let possible_funcs: Vec<FunctionNode> = match ty {
                VarType::User(TypeNode::Contract(con_node), _) => con_node.funcs(self),
                VarType::BuiltIn(bn, _) => self
                    .possible_library_funcs(ctx, bn.0.into())
                    .into_iter()
                    .collect::<Vec<_>>(),
                VarType::Concrete(cnode) => {
                    let b = cnode.underlying(self).as_builtin();
                    let bn = self.builtin_or_add(b);
                    self.possible_library_funcs(ctx, bn)
                        .into_iter()
                        .collect::<Vec<_>>()
                }
                VarType::User(TypeNode::Struct(sn), _) => self
                    .possible_library_funcs(ctx, sn.0.into())
                    .into_iter()
                    .collect::<Vec<_>>(),
                VarType::User(TypeNode::Enum(en), _) => self
                    .possible_library_funcs(ctx, en.0.into())
                    .into_iter()
                    .collect::<Vec<_>>(),
                VarType::User(TypeNode::Func(_), _) => todo!(),
            };
            let lits = input_exprs
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
                .collect();

            if let Some(func) =
                self.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs[..])
            {
                self.setup_fn_call(loc, &inputs, func.into(), ctx, Some(func_str))
            } else {
                panic!(
                    "Could not disambiguate function call: {}, {:?}",
                    ident.name, inputs
                )
            }
        }
    }
}