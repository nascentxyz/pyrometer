use crate::context::exprs::IntoExprErr;
use crate::context::ExprErr;
use crate::{func_call::FuncCaller, ContextBuilder};
use shared::context::ExprRet;
use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::{ContextEdge, ContextNode, ContextVar, ContextVarNode},
    Edge, Node,
};
use solang_parser::pt::{
    Expression,
    Expression::{HexLiteral, Negate, NumberLiteral},
    Identifier, Loc, NamedArgument,
};

impl<T> InternalFuncCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
}
pub trait InternalFuncCaller:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike
{
    fn call_internal_named_func(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        ident: &Identifier,
        // _func_expr: &Expression,
        input_args: &[NamedArgument],
    ) -> Result<(), ExprErr> {
        // It is a function call, check if we have the ident in scope
        let funcs = ctx.visible_funcs(self).into_expr_err(*loc)?;
        // filter down all funcs to those that match
        let possible_funcs = funcs
            .iter()
            .filter(|func| {
                let named_correctly = func
                    .name(self)
                    .unwrap()
                    .starts_with(&format!("{}(", ident.name));
                if !named_correctly {
                    false
                } else {
                    // filter by params
                    let params = func.params(self);
                    if params.len() != input_args.len() {
                        false
                    } else {
                        params.iter().all(|param| {
                            input_args
                                .iter()
                                .any(|input| input.name.name == param.name(self).unwrap())
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
                    let named_correctly = strukt
                        .name(self)
                        .unwrap()
                        .starts_with(&ident.name.to_string());
                    if !named_correctly {
                        false
                    } else {
                        // filter by params
                        let fields = strukt.fields(self);
                        if fields.len() != input_args.len() {
                            false
                        } else {
                            fields.iter().all(|field| {
                                input_args
                                    .iter()
                                    .any(|input| input.name.name == field.name(self).unwrap())
                            })
                        }
                    }
                })
                .copied()
                .collect::<Vec<_>>();
            if possible_structs.is_empty() {
                Err(ExprErr::FunctionNotFound(
                    *loc,
                    format!(
                        "No functions or structs found for named function call: {:?}",
                        ident.name
                    ),
                ))
            } else if possible_structs.len() == 1 {
                let strukt = possible_structs[0];
                let var =
                    ContextVar::new_from_struct(*loc, strukt, ctx, self).into_expr_err(*loc)?;
                let cvar = self.add_node(Node::ContextVar(var));
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

                strukt.fields(self).iter().try_for_each(|field| {
                    let field_cvar = ContextVar::maybe_new_from_field(
                        self,
                        *loc,
                        ContextVarNode::from(cvar)
                            .underlying(self)
                            .into_expr_err(*loc)?,
                        field.underlying(self).unwrap().clone(),
                    )
                    .expect("Invalid struct field");

                    let fc_node = self.add_node(Node::ContextVar(field_cvar));
                    self.add_edge(fc_node, cvar, Edge::Context(ContextEdge::AttrAccess));
                    self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                    let field_as_ret = ExprRet::Single(fc_node);
                    let input = input_args
                        .iter()
                        .find(|arg| arg.name.name == field.name(self).unwrap())
                        .expect("No field in struct in struct construction");
                    self.parse_ctx_expr(&input.expr, ctx)?;
                    self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                        let Some(assignment) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoRhs(loc, "Array creation failed".to_string()))
                        };
                        analyzer.match_assign_sides(ctx, loc, &field_as_ret, &assignment)?;
                        let _ = ctx.pop_expr(loc, analyzer).into_expr_err(loc)?;
                        Ok(())
                    })
                })?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, _loc| {
                    println!("ADDING STRUCT TO CTX STACK");
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(*loc)?;
                    println!("ADDED TO {}", ctx.path(analyzer));
                    Ok(())
                })?;
                Ok(())
            } else {
                todo!("Disambiguate struct construction");
            }
        } else if possible_funcs.len() == 1 {
            let func = possible_funcs[0];
            let params = func.params(self);
            let inputs: Vec<_> = params
                .iter()
                .map(|param| {
                    let input = input_args
                        .iter()
                        .find(|arg| arg.name.name == param.name(self).unwrap())
                        .expect(
                            "No parameter with named provided in named parameter function call",
                        );
                    input.expr.clone()
                })
                .collect();
            self.parse_inputs(ctx, *loc, &inputs[..])?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let inputs = ctx
                    .pop_expr(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or_else(|| ExprRet::Multi(vec![]));
                analyzer.setup_fn_call(&ident.loc, &inputs, func.into(), ctx, None)
            })
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
    ) -> Result<(), ExprErr> {
        tracing::trace!("function call: {}(..)", ident.name);
        // It is a function call, check if we have the ident in scope
        let funcs = ctx.visible_funcs(self).into_expr_err(*loc)?;
        // println!("visible funcs: [{:#?}]", funcs.iter().map(|i| i.name(self)).collect::<Vec<_>>());
        // println!("visible funcs: [{:#?}], looking for: {}, path: {}", funcs.iter().map(|func| func.name(self)).collect::<Vec<_>>(), ident.name, ctx.path(self));
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
        // println!("possible_funcs: [{:#?}]", possible_funcs.iter().map(|i| i.name(self)).collect::<Vec<_>>());

        if possible_funcs.is_empty() {
            // this is a builtin, cast, or unknown function?
            self.parse_ctx_expr(func_expr, ctx)?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let ret = ctx
                    .pop_expr(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or_else(|| ExprRet::Multi(vec![]));
                analyzer.match_intrinsic_fallback(ctx, &loc, input_exprs, ret)
            })
        } else if possible_funcs.len() == 1 {
            self.parse_inputs(ctx, *loc, input_exprs)?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let inputs = ctx
                    .pop_expr(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or_else(|| ExprRet::Multi(vec![]));
                analyzer.setup_fn_call(&ident.loc, &inputs, (possible_funcs[0]).into(), ctx, None)
            })
        } else {
            // this is the annoying case due to function overloading & type inference on number literals
            let lits: Vec<_> = input_exprs
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

            self.parse_inputs(ctx, *loc, input_exprs)?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let inputs = ctx
                    .pop_expr(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or_else(|| ExprRet::Multi(vec![]));
                if let Some(func) = analyzer.disambiguate_fn_call(
                    &ident.name,
                    lits.clone(),
                    &inputs,
                    &possible_funcs,
                ) {
                    analyzer.setup_fn_call(&loc, &inputs, func.into(), ctx, None)
                } else {
                    Err(ExprErr::FunctionNotFound(
                        loc,
                        "Could not find function".to_string(),
                    ))
                }
            })
        }
    }
}
