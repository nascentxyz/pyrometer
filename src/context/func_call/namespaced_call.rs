use crate::context::{
    exprs::{IntoExprErr, MemberAccess},
    func_call::intrinsic_call::IntrinsicFuncCaller,
    func_call::FuncCaller,
    ContextBuilder, ExprErr,
};
use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::{ContextNode, ContextVarNode, ExprRet},
    nodes::FunctionNode,
    Node, NodeIdx,
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
        tracing::trace!("Calling name spaced function");
        if let Variable(Identifier { name, .. }) = member_expr {
            if name == "abi" {
                let func_name = format!("abi.{}", ident.name);
                let fn_node = self
                    .builtin_fn_or_maybe_add(&func_name)
                    .unwrap_or_else(|| panic!("No builtin function with name {func_name}"));
                return self.intrinsic_func_call(loc, input_exprs, fn_node, ctx);
            } else if name == "super" {
                if let Some(contract) = ctx.maybe_associated_contract(self).into_expr_err(*loc)? {
                    let supers = contract.super_contracts(self);
                    let possible_funcs: Vec<_> = supers
                        .iter()
                        .filter_map(|con_node| {
                            con_node.funcs(self).into_iter().find(|func_node| {
                                func_node.name(self).unwrap().starts_with(&ident.name)
                            })
                        })
                        .collect();

                    if possible_funcs.is_empty() {
                        return Err(ExprErr::FunctionNotFound(
                            *loc,
                            "Could not find function in super".to_string(),
                        ));
                    }
                    self.parse_inputs(ctx, *loc, input_exprs)?;
                    return self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                        let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Namespace function call had no inputs".to_string()))
                        };
                        if possible_funcs.len() == 1 {
                            let mut inputs = inputs.as_vec();
                            let func = possible_funcs[0];
                            if func.params(analyzer).len() < inputs.len() {
                                inputs = inputs[1..].to_vec();
                            }
                            let inputs = ExprRet::Multi(inputs);
                            if inputs.has_killed() {
                                return ctx.kill(analyzer, loc, inputs.killed_kind().unwrap()).into_expr_err(loc);
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
                                return ctx.kill(analyzer, loc, inputs.killed_kind().unwrap()).into_expr_err(loc);
                            }
                            if let Some(func) =
                                analyzer.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
                            {
                                analyzer.setup_fn_call(&loc, &inputs, func.into(), ctx, None)
                            } else {
                                Err(ExprErr::FunctionNotFound(
                                    loc,
                                    "Could not find function in super".to_string(),
                                ))
                            }
                        }
                    });
                }
            }
        }

        self.parse_ctx_expr(member_expr, ctx)?;
        self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "Namespace function call had no namespace".to_string()))
            };

            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }

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
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Null => Err(ExprErr::NoLhs(
                loc,
                "No function found due to null".to_string(),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
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

        let funcs = self.visible_member_funcs(ctx, loc, member)?;
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
            let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(loc, "Namespace function call had no inputs".to_string()))
            };

            if matches!(inputs, ExprRet::CtxKilled(_)) {
                ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            // let mut inputs = inputs.as_vec();

            // let inputs = ExprRet::Multi(inputs);
            println!("possible_funcs: {:?}", possible_funcs);
            if possible_funcs.is_empty() {
                // TODO: this is extremely ugly.
                if inputs.has_killed() {
                    return ctx.kill(analyzer, loc, inputs.killed_kind().unwrap()).into_expr_err(loc);
                }
                let mut inputs = inputs.as_vec();
                if let Node::ContextVar(_) = analyzer.node(member) { inputs.insert(0, ExprRet::Single(member)) }
                let inputs = ExprRet::Multi(inputs);

                let as_input_str = inputs.try_as_func_input_str(analyzer);

                let lits = inputs.literals_list().into_expr_err(loc)?;
                if lits.iter().any(|i| *i) {
                    // try to disambiguate
                    if lits[0] {
                        Err(ExprErr::Todo(loc, "First element in function call was literal".to_string()))
                    } else {
                        let ty = if let Node::ContextVar(cvar) = analyzer.node(member) {
                            cvar.ty.ty_idx()
                        } else {
                            member
                        };

                        let possible_builtins: Vec<_> = analyzer.builtin_fn_inputs().iter().filter_map(|(func_name, (inputs, _))| {
                            if func_name.starts_with(&ident.name) {
                                if let Some(input) = inputs.first() {
                                    if input.ty == ty {
                                        Some(func_name.clone())
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }).collect::<Vec<_>>();
                        let possible_builtins: Vec<_> = possible_builtins.into_iter().filter_map(|name| {
                            analyzer.builtin_fn_or_maybe_add(&name).map(FunctionNode::from)
                        }).collect();
                        if let Some(func) =
                            analyzer.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_builtins)
                        {
                            let expr = &MemberAccess(
                                loc,
                                Box::new(member_expr.clone()),
                                Identifier {
                                    loc: ident.loc,
                                    name: func.name(analyzer).into_expr_err(loc)?.split('(').collect::<Vec<_>>()[0].to_string(),
                                },
                            );
                            analyzer.parse_ctx_expr(expr, ctx)?;
                            analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoLhs(loc, "Fallback function parse failure".to_string()))
                                };
                                if matches!(ret, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                let mut modifier_input_exprs = vec![member_expr.clone()];
                                modifier_input_exprs.extend(input_exprs.to_vec());
                                analyzer.match_intrinsic_fallback(ctx, &loc, &modifier_input_exprs, ret)
                            })
                        } else {
                            Err(ExprErr::FunctionNotFound(
                                loc,
                                format!("Could not disambiguate function, possible functions: {:#?}", possible_builtins.iter().map(|i| i.name(analyzer).unwrap()).collect::<Vec<_>>())
                            ))
                        }
                    }
                } else {
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
                        let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                            return Err(ExprErr::NoLhs(loc, "Fallback function parse failure".to_string()))
                        };
                        if matches!(ret, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }
                        let mut modifier_input_exprs = vec![member_expr.clone()];
                        modifier_input_exprs.extend(input_exprs.to_vec());
                        analyzer.match_intrinsic_fallback(ctx, &loc, &modifier_input_exprs, ret)
                    })
                }
            } else if possible_funcs.len() == 1 {
                let mut inputs = inputs.as_vec();
                let func = possible_funcs[0];
                if func.params(analyzer).len() > inputs.len() {
                    // Add the member back in if its a context variable
                    if let Node::ContextVar(_) = analyzer.node(member) { inputs.insert(0, ExprRet::Single(member)) }
                }
                let inputs = ExprRet::Multi(inputs);
                if inputs.has_killed() {
                    return ctx.kill(analyzer, loc, inputs.killed_kind().unwrap()).into_expr_err(loc);
                }


                analyzer.setup_fn_call(&ident.loc, &inputs, func.into(), ctx, None)
            } else {
                // Add the member back in if its a context variable
                let mut inputs = inputs.as_vec();
                if let Node::ContextVar(_) = analyzer.node(member) { inputs.insert(0, ExprRet::Single(member)) }
                let inputs = ExprRet::Multi(inputs);
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
                    return ctx.kill(analyzer, loc, inputs.killed_kind().unwrap()).into_expr_err(loc);
                }
                if let Some(func) =
                    analyzer.disambiguate_fn_call(&ident.name, lits, &inputs, &possible_funcs)
                {
                    analyzer.setup_fn_call(&loc, &inputs, func.into(), ctx, None)
                } else {
                    Err(ExprErr::FunctionNotFound(
                        loc,
                        format!("Could not disambiguate function, possible functions: {:#?}", possible_funcs.iter().map(|i| i.name(analyzer).unwrap()).collect::<Vec<_>>())
                    ))
                }
            }
        })
    }
}
