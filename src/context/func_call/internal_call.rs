
use solang_parser::pt::{Loc, Identifier, Expression, Expression::{Negate, HexLiteral, NumberLiteral}, NamedArgument};
use crate::{
    ExprRet,
    func_call::{intrinsic_call::IntrinsicFuncCaller, FuncCaller},
    ContextBuilder,
};
use shared::{Edge, Node, context::{ContextVarNode, ContextVar, ContextNode, ContextEdge,}, analyzer::{AnalyzerLike, GraphLike}};


impl<T> InternalFuncCaller for T where T: AnalyzerLike<Expr = Expression> + Sized + GraphLike  {}
pub trait InternalFuncCaller: AnalyzerLike<Expr = Expression> + Sized + GraphLike  {
    fn call_internal_named_func(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        ident: &Identifier,
        // _func_expr: &Expression,
        input_args: &[NamedArgument],
    ) -> ExprRet {
        // It is a function call, check if we have the ident in scope
        let funcs = ctx.visible_funcs(self);
        // filter down all funcs to those that match
        let possible_funcs = funcs
            .iter()
            .filter(|func| {
                let named_correctly = func.name(self).starts_with(&format!("{}(", ident.name));
                if !named_correctly {
                    false
                } else {
                    // filter by params
                    let params = func.params(self);
                    if params.len() != input_args.len() {
                        false
                    } else {
                        params.iter().all(|param| {
                            input_args.iter().any(|input| input.name.name == param.name(self))
                        })
                    }
                }
            })
            .copied()
            .collect::<Vec<_>>();

        if possible_funcs.is_empty() {
            // check structs
            let structs = ctx.visible_structs(self);
            let possible_structs = structs
                .iter()
                .filter(|strukt| {
                    let named_correctly = strukt.name(self).starts_with(&ident.name.to_string());
                    if !named_correctly {
                        false
                    } else {
                        // filter by params
                        let fields = strukt.fields(self);
                        if fields.len() != input_args.len() {
                            false
                        } else {
                            fields.iter().all(|field| {
                                input_args.iter().any(|input| input.name.name == field.name(self))
                            })
                        }
                    }
                })
                .copied()
                .collect::<Vec<_>>();
            if possible_structs.is_empty() {
                panic!("No functions or structs found for Named Function Call");
            } else if possible_structs.len() == 1 {
                let strukt = possible_structs[0];
                let var = ContextVar::new_from_struct(*loc, strukt, ctx, self);
                let cvar = self.add_node(Node::ContextVar(var));
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

                strukt.fields(self).iter().for_each(|field| {
                    let field_cvar = ContextVar::maybe_new_from_field(
                        self,
                        *loc,
                        ContextVarNode::from(cvar).underlying(self),
                        field.underlying(self).clone(),
                    ).expect("Invalid struct field");

                    let fc_node = self.add_node(Node::ContextVar(field_cvar));
                    self.add_edge(
                        fc_node,
                        cvar,
                        Edge::Context(ContextEdge::AttrAccess),
                    );
                    self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                    let field_as_ret = ExprRet::Single((ctx, fc_node));
                    let input = input_args.iter().find(|arg| arg.name.name == field.name(self)).expect("No field in struct in struct construction");
                    let assignment = self.parse_ctx_expr(&input.expr, ctx);
                    self.match_assign_sides(
                        *loc,
                        &field_as_ret,
                        &assignment
                    );
                });
                ExprRet::Single((ctx, cvar))
            } else {
                todo!("Disambiguate struct construction");
            }
        } else if possible_funcs.len() == 1 {
            let func = possible_funcs[0];
            let params = func.params(self);
            let inputs = ExprRet::Multi(params
                    .iter()
                    .map(|param| {
                        let input = input_args.iter().find(|arg| arg.name.name == param.name(self)).expect("No parameter with named provided in named parameter function call");
                        self.parse_ctx_expr(&input.expr, ctx)
                    })
                    .collect()
            );
            self.setup_fn_call(&ident.loc, &inputs, func.into(), ctx, None)
        } else {
            todo!("Disambiguate named function call");
        }
    }

	fn call_internal_func(
		&mut self,
		ctx: ContextNode,
        loc: &Loc,
        ident: &Identifier,
        func_expr: &Expression,
        input_exprs: &[Expression],
    ) -> ExprRet {
        // It is a function call, check if we have the ident in scope
        let funcs = ctx.visible_funcs(self);
        // filter down all funcs to those that match
        let possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).starts_with(&format!("{}(", ident.name)))
            .copied()
            .collect::<Vec<_>>();

        if possible_funcs.is_empty() {
            // this is a builtin, cast, or unknown function?
            let (func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                ExprRet::Single((ctx, idx)) => (ctx, idx),
                m @ ExprRet::Multi(_) => m.expect_single(),
                ExprRet::CtxKilled => return ExprRet::CtxKilled,
                e => todo!("got fork in func call: {:?}", e),
            };
            self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
        } else if possible_funcs.len() == 1 {
            let inputs = ExprRet::Multi(
                input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect(),
            );
            self.setup_fn_call(&ident.loc, &inputs, (possible_funcs[0]).into(), ctx, None)
        } else {
            // this is the annoying case due to function overloading & type inference on number literals
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
            let inputs = ExprRet::Multi(
                input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect(),
            );

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