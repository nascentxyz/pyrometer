use crate::func_caller::NamedOrUnnamedArgs;
use crate::ListAccess;
use crate::{variable::Variable, ContextBuilder, ExpressionParser};
use graph::nodes::FunctionNode;

use graph::{
    elem::*,
    nodes::{
        BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, TyNode,
    },
    AnalyzerBackend, Node, VarType,
};
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> TypesCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling type-based intrinsic functions, like `wrap`
pub trait TypesCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform a type-based intrinsic function call, like `wrap`
    fn types_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_name: String,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "type" => self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx),
            "wrap" => {
                if input_exprs.len() != 2 {
                    return Err(ExprErr::InvalidFunctionInput(loc, format!("Expected a member type and an input to the wrap function, but got: {:?}", input_exprs)));
                }

                input_exprs.parse(arena, self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
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
                    next.set_range_min(analyzer, arena, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, arena, expr)
                        .into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(cvar.into()), analyzer)
                        .into_expr_err(loc)
                })
            }
            "unwrap" => {
                input_exprs.parse(arena, self, ctx, loc)?;
                self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
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
                    cvar.set_range_min(analyzer, arena, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    cvar.set_range_max(analyzer, arena, Elem::from(to_be_unwrapped))
                        .into_expr_err(loc)?;
                    let next = analyzer.advance_var_in_ctx(cvar, loc, ctx)?;
                    let expr = Elem::Expr(RangeExpr::new(
                        Elem::from(to_be_unwrapped),
                        RangeOp::Cast,
                        Elem::from(cvar),
                    ));
                    next.set_range_min(analyzer, arena, expr.clone())
                        .into_expr_err(loc)?;
                    next.set_range_max(analyzer, arena, expr)
                        .into_expr_err(loc)?;
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
        arena: &mut RangeArena<Elem<Concrete>>,
        ty: Builtin,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Cast had no target type".to_string()));
            };

            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }

            let var_ty = VarType::try_from_idx(analyzer, func_idx).unwrap();
            analyzer.cast_inner(arena, ctx, var_ty, &ty, ret, loc)
        })
    }

    fn cast_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        var_ty: VarType,
        ty: &Builtin,
        ret: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match ret {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Null => Ok(()),
            ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                let cvar = ContextVarNode::from(cvar);
                let new_var = cvar
                    .as_cast_tmp(loc, ctx, ty.clone(), self)
                    .into_expr_err(loc)?;

                let maybe_new_range = cvar.cast_exprs(&var_ty, self, arena).into_expr_err(loc)?;
                new_var.underlying_mut(self).into_expr_err(loc)?.ty = var_ty;

                if let Some((new_min, new_max)) = maybe_new_range {
                    new_var
                        .set_range_min(self, arena, new_min)
                        .into_expr_err(loc)?;
                    new_var
                        .set_range_max(self, arena, new_max)
                        .into_expr_err(loc)?;
                }

                if cvar.needs_length(self).into_expr_err(loc)? {
                    // input is indexable. get the length attribute, create a new length for the casted type
                    let _ = self.create_length(
                        arena,
                        ctx,
                        loc,
                        new_var,
                        new_var.latest_version(self),
                        false,
                    )?;
                }

                ctx.push_expr(ExprRet::Single(new_var.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::Multi(inner) => inner
                .into_iter()
                .try_for_each(|i| self.cast_inner(arena, ctx, var_ty.clone(), ty, i, loc)),
        }
    }
}
