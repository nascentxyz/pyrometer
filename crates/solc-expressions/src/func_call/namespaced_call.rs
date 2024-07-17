//! Traits & blanket implementations that facilitate performing namespaced function calls.

use crate::assign::Assign;
use crate::{
    func_call::func_caller::{FuncCaller, NamedOrUnnamedArgs},
    func_call::helper::CallerHelper,
    member_access::MemberAccess,
    ContextBuilder, ExpressionParser,
};
use graph::nodes::{Concrete, ContextVar};
use graph::ContextEdge;
use graph::Edge;
use graph::VarType;

use graph::{
    elem::Elem,
    nodes::{ContextNode, ContextVarNode, ExprRet, FunctionNode},
    AnalyzerBackend, GraphBackend, Node,
};

use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> NameSpaceFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
}
/// A trait for performing namespaced function calls (i.e. `MyContract.myFunc(...)`)
pub trait NameSpaceFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
    #[tracing::instrument(level = "trace", skip_all)]
    /// Call a namedspaced function, i.e. `MyContract.myFunc(...)`
    fn call_name_spaced_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: &Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: NamedOrUnnamedArgs,
    ) -> Result<(), ExprErr> {
        unreachable!("Should not have reached this");
        // use solang_parser::pt::Expression::*;
        // tracing::trace!("Calling name spaced function");
        // if let Variable(Identifier { name, .. }) = member_expr {
        //     if name == "abi" {
        //         let func_name = format!("abi.{}", ident.name);
        //         let fn_node = self
        //             .builtin_fn_or_maybe_add(&func_name)
        //             .unwrap_or_else(|| panic!("No builtin function with name {func_name}"));
        //         unreachable!()
        //     } else if name == "super" {
        //         if let Some(contract) = ctx.maybe_associated_contract(self).into_expr_err(*loc)? {
        //             let supers = contract.super_contracts(self);
        //             let possible_funcs: Vec<_> = supers
        //                 .iter()
        //                 .filter_map(|con_node| {
        //                     con_node
        //                         .linearized_functions(self)
        //                         .ok()?
        //                         .into_iter()
        //                         .find(|(func_name, _func_node)| func_name.starts_with(&ident.name))
        //                         .map(|(_, node)| node)
        //                 })
        //                 .collect();

        //             if possible_funcs.is_empty() {
        //                 return Err(ExprErr::FunctionNotFound(
        //                     *loc,
        //                     "Could not find function in super".to_string(),
        //                 ));
        //             }
        //             input_exprs.parse(arena, self, ctx, *loc)?;
        //             return self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
        //                 let inputs = if let Some(inputs) =
        //                     ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //                 {
        //                     inputs
        //                 } else {
        //                     ExprRet::Multi(vec![])
        //                 };
        //                 if possible_funcs.len() == 1 {
        //                     let mut inputs = if let Some(ordered_param_names) =
        //                         possible_funcs[0].maybe_ordered_param_names(analyzer)
        //                     {
        //                         input_exprs.order(inputs, ordered_param_names).as_vec()
        //                     } else {
        //                         inputs.as_vec()
        //                     };
        //                     let func = possible_funcs[0];
        //                     if func.params(analyzer).len() < inputs.len() {
        //                         inputs = inputs[1..].to_vec();
        //                     }
        //                     let inputs = ExprRet::Multi(inputs);
        //                     if inputs.has_killed() {
        //                         return ctx
        //                             .kill(analyzer, loc, inputs.killed_kind().unwrap())
        //                             .into_expr_err(loc);
        //                     }
        //                     analyzer.setup_fn_call(
        //                         arena,
        //                         &ident.loc,
        //                         &inputs,
        //                         func.into(),
        //                         ctx,
        //                         None,
        //                     )
        //                 } else {
        //                     // this is the annoying case due to function overloading & type inference on number literals
        //                     let mut lits = vec![false];
        //                     lits.extend(
        //                         input_exprs
        //                             .exprs()
        //                             .iter()
        //                             .map(|expr| {
        //                                 match expr {
        //                                     Negate(_, expr) => {
        //                                         // negative number potentially
        //                                         matches!(**expr, NumberLiteral(..) | HexLiteral(..))
        //                                     }
        //                                     NumberLiteral(..) | HexLiteral(..) => true,
        //                                     _ => false,
        //                                 }
        //                             })
        //                             .collect::<Vec<bool>>(),
        //                     );

        //                     if inputs.has_killed() {
        //                         return ctx
        //                             .kill(analyzer, loc, inputs.killed_kind().unwrap())
        //                             .into_expr_err(loc);
        //                     }
        //                     if let Some(func) = analyzer.disambiguate_fn_call(
        //                         arena,
        //                         &ident.name,
        //                         lits,
        //                         &inputs,
        //                         &possible_funcs,
        //                         None,
        //                     ) {
        //                         analyzer.setup_fn_call(arena, &loc, &inputs, func.into(), ctx, None)
        //                     } else {
        //                         Err(ExprErr::FunctionNotFound(
        //                             loc,
        //                             "Could not find function in super".to_string(),
        //                         ))
        //                     }
        //                 }
        //             });
        //         }
        //     }
        // }

        // self.parse_ctx_expr(arena, member_expr, ctx)?;
        // self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
        //     let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
        //         return Err(ExprErr::NoLhs(
        //             loc,
        //             "Namespace function call had no namespace".to_string(),
        //         ));
        //     };

        //     if matches!(ret, ExprRet::CtxKilled(_)) {
        //         ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
        //         return Ok(());
        //     }

        //     analyzer.match_namespaced_member(arena, ctx, loc, member_expr, ident, &input_exprs, ret)
        // })
    }

    /// Match the expression return for getting the member node
    fn match_namespaced_member(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &NamedOrUnnamedArgs,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => self
                .call_name_spaced_func_inner(
                    arena,
                    ctx,
                    loc,
                    member_expr,
                    ident,
                    input_exprs,
                    inner,
                    true,
                ),
            ExprRet::Multi(inner) => inner.into_iter().try_for_each(|ret| {
                self.match_namespaced_member(arena, ctx, loc, member_expr, ident, input_exprs, ret)
            }),
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Null => Err(ExprErr::NoLhs(
                loc,
                "No function found due to null".to_string(),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Actually perform the namespaced function call
    fn call_name_spaced_func_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        member_expr: &Expression,
        ident: &Identifier,
        input_exprs: &NamedOrUnnamedArgs,
        member: NodeIdx,
        member_is_lit: bool,
    ) -> Result<(), ExprErr> {
        unreachable!("Should not have called this");
        // use solang_parser::pt::Expression::*;
        // tracing::trace!(
        //     "namespaced function call: {:?}.{:?}(..)",
        //     ContextVarNode::from(member).display_name(self),
        //     ident.name
        // );

        // let funcs = self.visible_member_funcs(ctx, loc, member)?;
        // // filter down all funcs to those that match
        // let possible_funcs = funcs
        //     .iter()
        //     .filter(|func| {
        //         func.name(self)
        //             .unwrap()
        //             .starts_with(&format!("{}(", ident.name))
        //     })
        //     .copied()
        //     .collect::<Vec<_>>();

        // ctx.push_expr(ExprRet::Single(member), self)
        //     .into_expr_err(loc)?;

        // input_exprs.parse(arena, self, ctx, loc)?;
        // self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
        //     let Some(mut inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
        //         return Err(ExprErr::NoLhs(
        //             loc,
        //             "Namespace function call had no inputs".to_string(),
        //         ));
        //     };

        //     if matches!(inputs, ExprRet::CtxKilled(_)) {
        //         ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
        //         return Ok(());
        //     }
        //     if possible_funcs.is_empty() {
        //         // check structs
        //         let structs = ctx.visible_structs(analyzer).into_expr_err(loc)?;
        //         let possible_structs = structs
        //             .iter()
        //             .filter(|strukt| {
        //                 let named_correctly = strukt
        //                     .name(analyzer)
        //                     .unwrap()
        //                     .starts_with(&ident.name.to_string());
        //                 if !named_correctly {
        //                     false
        //                 } else {
        //                     // filter by params
        //                     let fields = strukt.fields(analyzer);
        //                     fields.len() == input_exprs.len()
        //                 }
        //             })
        //             .copied()
        //             .collect::<Vec<_>>();

        //         if possible_structs.len() == 1 {
        //             let strukt = possible_structs[0];
        //             let var = ContextVar::new_from_struct(loc, strukt, ctx, analyzer)
        //                 .into_expr_err(loc)?;
        //             let cvar = analyzer.add_node(Node::ContextVar(var));
        //             ctx.add_var(cvar.into(), analyzer).into_expr_err(loc)?;
        //             analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));

        //             strukt.fields(analyzer).iter().try_for_each(|field| {
        //                 let field_cvar = ContextVar::maybe_new_from_field(
        //                     analyzer,
        //                     loc,
        //                     ContextVarNode::from(cvar)
        //                         .underlying(analyzer)
        //                         .into_expr_err(loc)?,
        //                     field.underlying(analyzer).unwrap().clone(),
        //                 )
        //                 .expect("Invalid struct field");

        //                 let fc_node = analyzer.add_node(Node::ContextVar(field_cvar));
        //                 analyzer.add_edge(fc_node, cvar, Edge::Context(ContextEdge::AttrAccess("field")));
        //                 analyzer.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
        //                 ctx.add_var(fc_node.into(), analyzer).into_expr_err(loc)?;
        //                 let field_as_ret = ExprRet::Single(fc_node);
        //                 let Some(assignment) = inputs.take_one().into_expr_err(loc)? else {
        //                     return Err(ExprErr::NoRhs(loc, "Struct creation failed".to_string()));
        //                 };

        //                 if matches!(assignment, ExprRet::CtxKilled(_)) {
        //                     ctx.push_expr(assignment, analyzer).into_expr_err(loc)?;
        //                     return Ok(());
        //                 }

        //                 analyzer.match_assign_sides(arena, ctx, loc, &field_as_ret, &assignment)?;
        //                 let _ = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
        //                 Ok(())
        //             })?;
        //             analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, _arena, ctx, _loc| {
        //                 ctx.push_expr(ExprRet::Single(cvar), analyzer)
        //                     .into_expr_err(loc)?;
        //                 Ok(())
        //             })?;
        //             return Ok(());
        //         }
        //         // TODO: this is extremely ugly.
        //         if inputs.has_killed() {
        //             return ctx
        //                 .kill(analyzer, loc, inputs.killed_kind().unwrap())
        //                 .into_expr_err(loc);
        //         }
        //         let mut inputs = inputs.as_vec();
        //         if let Node::ContextVar(_) = analyzer.node(member) {
        //             inputs.insert(0, ExprRet::Single(member))
        //         }
        //         if let Node::ContextVar(_) = analyzer.node(member) {
        //             if member_is_lit {
        //                 inputs.insert(0, ExprRet::SingleLiteral(member))
        //             } else {
        //                 inputs.insert(0, ExprRet::Single(member))
        //             }
        //         }
        //         let inputs = ExprRet::Multi(inputs);

        //         let as_input_str = inputs.try_as_func_input_str(analyzer, arena);

        //         let lits = inputs.literals_list().into_expr_err(loc)?;
        //         if lits.iter().any(|i| *i) {
        //             // try to disambiguate
        //             let ty = if let Node::ContextVar(cvar) = analyzer.node(member) {
        //                 cvar.ty.ty_idx()
        //             } else {
        //                 member
        //             };

        //             let possible_builtins: Vec<_> = analyzer
        //                 .builtin_fn_inputs()
        //                 .iter()
        //                 .filter_map(|(func_name, (inputs, _))| {
        //                     if func_name.starts_with(&ident.name) {
        //                         if let Some(input) = inputs.first() {
        //                             let try_cast = VarType::try_from_idx(analyzer, ty)?
        //                                 .implicitly_castable_to(
        //                                     &VarType::try_from_idx(analyzer, input.ty)?,
        //                                     analyzer,
        //                                 );
        //                             let Ok(implicitly_castable) = try_cast else {
        //                                 return None;
        //                             };
        //                             if implicitly_castable {
        //                                 Some(func_name.clone())
        //                             } else {
        //                                 None
        //                             }
        //                         } else {
        //                             // generic builtin function, return it
        //                             Some(func_name.clone())
        //                         }
        //                     } else {
        //                         None
        //                     }
        //                 })
        //                 .collect::<Vec<_>>();
        //             let possible_builtins: Vec<_> = possible_builtins
        //                 .into_iter()
        //                 .filter_map(|name| {
        //                     analyzer
        //                         .builtin_fn_or_maybe_add(&name)
        //                         .map(FunctionNode::from)
        //                 })
        //                 .collect();

        //             let maybe_func = if possible_builtins.len() == 1 {
        //                 Some(possible_builtins[0])
        //             } else {
        //                 analyzer.disambiguate_fn_call(
        //                     arena,
        //                     &ident.name,
        //                     lits,
        //                     &inputs,
        //                     &possible_builtins,
        //                 )
        //             };
        //             if let Some(func) = maybe_func {
        //                 let expr = &MemberAccess(
        //                     loc,
        //                     Box::new(member_expr.clone()),
        //                     Identifier {
        //                         loc: ident.loc,
        //                         name: func
        //                             .name(analyzer)
        //                             .into_expr_err(loc)?
        //                             .split('(')
        //                             .collect::<Vec<_>>()[0]
        //                             .to_string(),
        //                     },
        //                 );
        //                 analyzer.parse_ctx_expr(arena, expr, ctx)?;
        //                 analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
        //                     let Some(ret) =
        //                         ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //                     else {
        //                         return Err(ExprErr::NoLhs(
        //                             loc,
        //                             "Fallback function parse failure".to_string(),
        //                         ));
        //                     };
        //                     if matches!(ret, ExprRet::CtxKilled(_)) {
        //                         ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
        //                         return Ok(());
        //                     }
        //                     let mut modifier_input_exprs = vec![member_expr.clone()];
        //                     modifier_input_exprs.extend(input_exprs.exprs());
        //                     unreachable!()
        //                 })
        //             } else {
        //                 // analyzer.match_intrinsic_fallback(ctx, &loc, &modifier_input_exprs, ret)
        //                 Err(ExprErr::FunctionNotFound(
        //                     loc,
        //                     format!(
        //                         "Could not disambiguate builtin function, possible builtin functions: {:#?}",
        //                         possible_builtins
        //                             .iter()
        //                             .map(|i| i.name(analyzer).unwrap())
        //                             .collect::<Vec<_>>()
        //                     ),
        //                 ))
        //             }
        //         } else {
        //             let expr = &MemberAccess(
        //                 loc,
        //                 Box::new(member_expr.clone()),
        //                 Identifier {
        //                     loc: ident.loc,
        //                     name: format!("{}{}", ident.name, as_input_str),
        //                 },
        //             );
        //             analyzer.parse_ctx_expr(arena, expr, ctx)?;
        //             analyzer.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
        //                 let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //                 else {
        //                     return Err(ExprErr::NoLhs(
        //                         loc,
        //                         "Fallback function parse failure".to_string(),
        //                     ));
        //                 };
        //                 if matches!(ret, ExprRet::CtxKilled(_)) {
        //                     ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
        //                     return Ok(());
        //                 }
        //                 let mut modifier_input_exprs = vec![member_expr.clone()];
        //                 modifier_input_exprs.extend(input_exprs.exprs());
        //                 unreachable!()
        //             })
        //         }
        //     } else if possible_funcs.len() == 1 {
        //         let mut inputs = if let Some(ordered_param_names) =
        //             possible_funcs[0].maybe_ordered_param_names(analyzer)
        //         {
        //             input_exprs.order(inputs, ordered_param_names).as_vec()
        //         } else {
        //             inputs.as_vec()
        //         };
        //         let func = possible_funcs[0];
        //         if func.params(analyzer).len() > inputs.len() {
        //             // Add the member back in if its a context variable
        //             if let Node::ContextVar(_) = analyzer.node(member) {
        //                 inputs.insert(0, ExprRet::Single(member))
        //             }
        //         }
        //         let inputs = ExprRet::Multi(inputs);
        //         if inputs.has_killed() {
        //             return ctx
        //                 .kill(analyzer, loc, inputs.killed_kind().unwrap())
        //                 .into_expr_err(loc);
        //         }

        //         analyzer.setup_fn_call(arena, &ident.loc, &inputs, func.into(), ctx, None)
        //     } else {
        //         // Add the member back in if its a context variable
        //         let mut inputs = inputs.as_vec();
        //         if let Node::ContextVar(_) = analyzer.node(member) {
        //             inputs.insert(0, ExprRet::Single(member))
        //         }
        //         let inputs = ExprRet::Multi(inputs);
        //         // this is the annoying case due to function overloading & type inference on number literals
        //         let mut lits = vec![false];
        //         lits.extend(
        //             input_exprs
        //                 .exprs()
        //                 .iter()
        //                 .map(|expr| {
        //                     match expr {
        //                         Negate(_, expr) => {
        //                             // negative number potentially
        //                             matches!(**expr, NumberLiteral(..) | HexLiteral(..))
        //                         }
        //                         NumberLiteral(..) | HexLiteral(..) => true,
        //                         _ => false,
        //                     }
        //                 })
        //                 .collect::<Vec<bool>>(),
        //         );

        //         if inputs.has_killed() {
        //             return ctx
        //                 .kill(analyzer, loc, inputs.killed_kind().unwrap())
        //                 .into_expr_err(loc);
        //         }
        //         if let Some(func) =
        //             analyzer.disambiguate_fn_call(arena, &ident.name, lits, &inputs, &possible_funcs)
        //         {
        //             analyzer.setup_fn_call(arena, &loc, &inputs, func.into(), ctx, None)
        //         } else {
        //             Err(ExprErr::FunctionNotFound(
        //                 loc,
        //                 format!(
        //                     "Could not disambiguate function, possible functions: {:#?}",
        //                     possible_funcs
        //                         .iter()
        //                         .map(|i| i.name(analyzer).unwrap())
        //                         .collect::<Vec<_>>()
        //                 ),
        //             ))
        //         }
        //     }
        // })
    }
}
