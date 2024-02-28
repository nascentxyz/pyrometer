use crate::ListAccess;
use crate::func_caller::NamedOrUnnamedArgs;
use crate::{variable::Variable, ContextBuilder, ExprErr, ExpressionParser, IntoExprErr};
use graph::nodes::FunctionNode;

use graph::{
    elem::*,
    nodes::{BuiltInNode, Builtin, ContextNode, ContextVar, ContextVarNode, ExprRet, TyNode},
    AnalyzerBackend, GraphBackend, Node, Range, VarType,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Loc};

impl<T> TypesCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling type-based intrinsic functions, like `wrap`
pub trait TypesCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a type-based intrinsic function call, like `wrap`
    fn types_call(
        &mut self,
        func_name: String,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "type" => self.parse_ctx_expr(&input_exprs.unnamed_args().unwrap()[0], ctx),
            "wrap" => {
                if input_exprs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(loc, format!("Expected a member type and an input to the wrap function, but got: {:?}", input_exprs)));
                }

                input_exprs.parse(self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "<type>.wrap(..) did not receive an input".to_string(),
                        ));
                    };

                    let input = if let Some(ordered_param_names) =
                        FunctionNode::from(func_idx).maybe_ordered_param_names(analyzer)
                    {
                        input_exprs.order(input, ordered_param_names)
                    } else {
                        input
                    };

                    input.expect_length(2).into_expr_err(loc)?;
                    let ret = input.as_vec();
                    let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                    let var =
                        ContextVar::new_from_ty(loc, TyNode::from(wrapping_ty), ctx, analyzer)
                            .into_expr_err(loc)?;
                    let to_be_wrapped = ret[1].expect_single().into_expr_err(loc)?;
                    let cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                    let next = analyzer.advance_var_in_ctx(cvar, loc, ctx)?;
                    let expr = Elem::Expr(RangeExpr::new(
                        Elem::from(to_be_wrapped),
                        RangeOp::Cast,
                        Elem::from(cvar),
                    ));
                    next.set_range_min(analyzer, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, expr).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(cvar.into()), analyzer)
                        .into_expr_err(loc)
                })
            }
            "unwrap" => {
                input_exprs.parse(self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "<type>.unwrap(..) did not receive an input".to_string(),
                        ));
                    };

                    let input = if let Some(ordered_param_names) =
                        FunctionNode::from(func_idx).maybe_ordered_param_names(analyzer)
                    {
                        input_exprs.order(input, ordered_param_names)
                    } else {
                        input
                    };

                    input.expect_length(2).into_expr_err(loc)?;
                    let ret = input.as_vec();
                    let wrapping_ty = ret[0].expect_single().into_expr_err(loc)?;
                    let mut var = ContextVar::new_from_builtin(
                        loc,
                        BuiltInNode::from(
                            TyNode::from(wrapping_ty)
                                .underlying(analyzer)
                                .into_expr_err(loc)?
                                .ty,
                        ),
                        analyzer,
                    )
                    .into_expr_err(loc)?;
                    let to_be_unwrapped = ret[1].expect_single().into_expr_err(loc)?;
                    var.display_name = format!(
                        "{}.unwrap({})",
                        TyNode::from(wrapping_ty)
                            .name(analyzer)
                            .into_expr_err(loc)?,
                        ContextVarNode::from(to_be_unwrapped)
                            .display_name(analyzer)
                            .into_expr_err(loc)?
                    );

                    let cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                    cvar.set_range_min(analyzer, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    cvar.set_range_max(analyzer, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    let next = analyzer.advance_var_in_ctx(cvar, loc, ctx)?;
                    let expr = Elem::Expr(RangeExpr::new(
                        Elem::from(to_be_unwrapped),
                        RangeOp::Cast,
                        Elem::from(cvar),
                    ));
                    next.set_range_min(analyzer, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, expr).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(cvar.into()), analyzer)
                        .into_expr_err(loc)
                })
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin types function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }

    /// Perform a cast of a type
    fn cast(
        &mut self,
        ty: Builtin,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        // it is a cast
        fn cast_match(
            ctx: ContextNode,
            loc: Loc,
            analyzer: &mut (impl GraphBackend + AnalyzerBackend + ListAccess),
            ty: &Builtin,
            ret: ExprRet,
            func_idx: NodeIdx,
        ) -> Result<(), ExprErr> {
            match ret {
                ExprRet::CtxKilled(kind) => ctx.kill(analyzer, loc, kind).into_expr_err(loc),
                ExprRet::Null => Ok(()),
                ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                    let cvar = ContextVarNode::from(cvar);
                    let new_var = cvar
                        .as_cast_tmp(loc, ctx, ty.clone(), analyzer)
                        .into_expr_err(loc)?;


                    let v_ty = VarType::try_from_idx(analyzer, func_idx).expect("");
                    let maybe_new_range = cvar.cast_exprs(&v_ty, analyzer).into_expr_err(loc)?;
                    new_var.underlying_mut(analyzer).into_expr_err(loc)?.ty = v_ty;

                    if let Some((new_min, new_max)) = maybe_new_range {
                        new_var
                            .set_range_min(analyzer, new_min)
                            .into_expr_err(loc)?;
                        new_var
                            .set_range_max(analyzer, new_max)
                            .into_expr_err(loc)?;
                    }

                    if cvar.is_indexable(analyzer).into_expr_err(loc)? {
                        // input is indexable. get the length attribute, create a new length for the casted type
                        let _ = analyzer.create_length(ctx, loc, cvar, new_var.latest_version(analyzer), false)?;
                    }

                    ctx.push_expr(ExprRet::Single(new_var.into()), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| cast_match(ctx, loc, analyzer, ty, i, func_idx)),
            }
        }

        self.parse_ctx_expr(&input_exprs.unnamed_args().unwrap()[0], ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Cast had no target type".to_string()));
            };

            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }

            cast_match(ctx, loc, analyzer, &ty, ret, func_idx)
        })
    }
}
