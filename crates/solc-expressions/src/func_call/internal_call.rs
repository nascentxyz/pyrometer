//! Traits & blanket implementations that facilitate performing locally scoped function calls.

use crate::func_caller::NamedOrUnnamedArgs;
use crate::{
    assign::Assign, func_call::func_caller::FuncCaller, helper::CallerHelper, ContextBuilder,
    ExpressionParser,
};

use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, VarType,
};
use shared::{ExprErr, GraphError, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Identifier, Loc, NamedArgument};

impl<T> InternalFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
}
/// A trait for performing internally scoped function calls (i.e. *NOT* `MyContract.func(...)`)
pub trait InternalFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
    #[tracing::instrument(level = "trace", skip_all)]
    /// Perform a named function call
    fn call_internal_named_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        ident: &Identifier,
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
            let structs = ctx.visible_structs(self).into_expr_err(*loc)?;
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
                let cvar = self.add_node(var);
                ctx.add_var(cvar.into(), self).into_expr_err(*loc)?;
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

                    let fc_node = self.add_node(field_cvar);
                    self.add_edge(
                        fc_node,
                        cvar,
                        Edge::Context(ContextEdge::AttrAccess("field")),
                    );
                    self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(fc_node.into(), self).into_expr_err(*loc)?;
                    let field_as_ret = ExprRet::Single(fc_node);
                    let input = input_args
                        .iter()
                        .find(|arg| arg.name.name == field.name(self).unwrap())
                        .expect("No field in struct in struct construction");
                    self.parse_ctx_expr(arena, &input.expr, ctx)?;
                    self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                        let Some(assignment) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoRhs(loc, "Array creation failed".to_string()));
                        };

                        if matches!(assignment, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(assignment, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        analyzer.match_assign_sides(arena, ctx, loc, &field_as_ret, &assignment)?;
                        let _ = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                        Ok(())
                    })
                })?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, _arena, ctx, _loc| {
                    ctx.push_expr(ExprRet::Single(cvar), analyzer)
                        .into_expr_err(*loc)?;
                    Ok(())
                })?;
                Ok(())
            } else {
                Err(ExprErr::Todo(
                    *loc,
                    "Disambiguation of struct construction not currently supported".to_string(),
                ))
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
            unreachable!()
        } else {
            todo!("Disambiguate named function call");
        }
    }

    fn find_super_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
    ) -> Result<Option<FunctionNode>, GraphError> {
        if let Some(contract) = ctx.maybe_associated_contract(self)? {
            let supers = contract.super_contracts(self);
            let possible_funcs: Vec<_> = supers
                .iter()
                .filter_map(|con_node| {
                    con_node
                        .linearized_functions(self)
                        .ok()?
                        .into_iter()
                        .find(|(func_name, func_node)| {
                            func_name.starts_with(&name)
                                && func_node.params(self).len() == num_inputs
                        })
                        .map(|(_, node)| node)
                })
                .collect();
            self.find_func_inner(arena, ctx, name, num_inputs, possible_funcs)
        } else {
            Ok(None)
        }
    }

    fn find_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
    ) -> Result<Option<FunctionNode>, GraphError> {
        let funcs = ctx.visible_funcs(self)?;
        let possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).unwrap().starts_with(&format!("{name}(")))
            .filter(|func| {
                // filter by params
                func.params(self).len() == num_inputs
            })
            .copied()
            .collect::<Vec<_>>();
        self.find_func_inner(arena, ctx, name, num_inputs, possible_funcs)
    }

    fn find_func_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
        possible_funcs: Vec<FunctionNode>,
    ) -> Result<Option<FunctionNode>, GraphError> {
        match possible_funcs.len() {
            0 => Ok(None),
            1 => Ok(Some(possible_funcs[0])),
            _ => {
                let stack = &ctx.underlying(self)?.expr_ret_stack;
                let len = stack.len();
                let inputs = &stack[len - num_inputs - 1..];
                let resizeables: Vec<_> = inputs
                    .iter()
                    .map(|input| input.expect_single().ok())
                    .map(|idx| {
                        let Some(idx) = idx else {
                            return false;
                        };
                        match VarType::try_from_idx(self, idx) {
                            Some(VarType::BuiltIn(bn, _)) => {
                                matches!(
                                    self.node(bn),
                                    Node::Builtin(Builtin::Uint(_))
                                        | Node::Builtin(Builtin::Int(_))
                                        | Node::Builtin(Builtin::Bytes(_))
                                )
                            }
                            Some(VarType::Concrete(c)) => {
                                matches!(
                                    self.node(c),
                                    Node::Concrete(Concrete::Uint(_, _))
                                        | Node::Concrete(Concrete::Int(_, _))
                                        | Node::Concrete(Concrete::Bytes(_, _))
                                )
                            }
                            _ => false,
                        }
                    })
                    .collect();

                let inputs = ExprRet::Multi(inputs.to_vec());
                Ok(self.disambiguate_fn_call(arena, &name, resizeables, &inputs, &possible_funcs))
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn call_internal_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        ident: &Identifier,
        func_expr: &Expression,
        input_exprs: NamedOrUnnamedArgs,
    ) -> Result<(), ExprErr> {
        tracing::trace!("function call: {}(..)", ident.name);
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
                    if params.len() != input_exprs.len() {
                        false
                    } else if matches!(input_exprs, NamedOrUnnamedArgs::Named(_)) {
                        params.iter().all(|param| {
                            input_exprs
                                .named_args()
                                .unwrap()
                                .iter()
                                .any(|input| input.name.name == param.name(self).unwrap())
                        })
                    } else {
                        true
                    }
                }
            })
            .copied()
            .collect::<Vec<_>>();

        match possible_funcs.len() {
            0 => {
                // this is a builtin, cast, or unknown function
                self.parse_ctx_expr(arena, func_expr, ctx)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let ret = ctx
                        .pop_expr_latest(loc, analyzer)
                        .into_expr_err(loc)?
                        .unwrap_or_else(|| ExprRet::Multi(vec![]));
                    let ret = ret.flatten();
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    unreachable!()
                })
            }
            1 => {
                // there is only a single possible function
                input_exprs.parse(arena, self, ctx, *loc)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let mut inputs = ctx
                        .pop_expr_latest(loc, analyzer)
                        .into_expr_err(loc)?
                        .unwrap_or_else(|| ExprRet::Multi(vec![]));
                    inputs = if let Some(ordered_param_names) =
                        possible_funcs[0].maybe_ordered_param_names(analyzer)
                    {
                        input_exprs.order(inputs, ordered_param_names)
                    } else {
                        inputs
                    };
                    let inputs = inputs.flatten();
                    if matches!(inputs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    analyzer.setup_fn_call(
                        arena,
                        &ident.loc,
                        &inputs,
                        (possible_funcs[0]).into(),
                        ctx,
                        None,
                    )
                })
            }
            _ => {
                // this is the annoying case due to function overloading & type inference on number literals
                input_exprs.parse(arena, self, ctx, *loc)?;
                self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    let inputs = ctx
                        .pop_expr_latest(loc, analyzer)
                        .into_expr_err(loc)?
                        .unwrap_or_else(|| ExprRet::Multi(vec![]));
                    let inputs = inputs.flatten();
                    if matches!(inputs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let resizeables: Vec<_> = inputs.as_flat_vec()
                        .iter()
                        .map(|idx| {
                            match VarType::try_from_idx(analyzer, *idx) {
                                Some(VarType::BuiltIn(bn, _)) => {
                                    matches!(analyzer.node(bn), Node::Builtin(Builtin::Uint(_)) | Node::Builtin(Builtin::Int(_)) | Node::Builtin(Builtin::Bytes(_)))
                                }
                                Some(VarType::Concrete(c)) => {
                                    matches!(analyzer.node(c), Node::Concrete(Concrete::Uint(_, _)) | Node::Concrete(Concrete::Int(_, _)) | Node::Concrete(Concrete::Bytes(_, _)))
                                }
                                _ => false
                            }
                        })
                        .collect();
                    if let Some(func) = analyzer.disambiguate_fn_call(
                        arena,
                        &ident.name,
                        resizeables,
                        &inputs,
                        &possible_funcs,
                    ) {
                        analyzer.setup_fn_call(arena, &loc, &inputs, func.into(), ctx, None)
                    } else {
                        Err(ExprErr::FunctionNotFound(
                            loc,
                            format!(
                                "Could not disambiguate function, default input types: {}, possible functions: {:#?}",
                                inputs.try_as_func_input_str(analyzer, arena),
                                possible_funcs
                                    .iter()
                                    .map(|i| i.name(analyzer).unwrap())
                                    .collect::<Vec<_>>()
                            ),
                        ))
                    }
                })
            }
        }
    }
}
