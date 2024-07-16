use crate::func_caller::NamedOrUnnamedArgs;
use crate::{assign::Assign, func_call::helper::CallerHelper, ContextBuilder, ExpressionParser};

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet, StructNode},
    AnalyzerBackend, ContextEdge, Edge, Node, Range, VarType,
};
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> ConstructorCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
}

/// Trait for constructing compound types like contracts, structs and arrays
pub trait ConstructorCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
    /// Construct an array
    fn construct_array(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        // create a new list
        self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let Some(len_var) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Array creation failed".to_string()));
            };

            if matches!(len_var, ExprRet::CtxKilled(_)) {
                ctx.push_expr(len_var, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.construct_array_inner(arena, func_idx, len_var, loc, ctx)
        })
    }

    fn construct_array_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_idx: NodeIdx,
        len_var: ExprRet,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let len_cvar = len_var.expect_single().into_expr_err(loc)?;

        let ty = VarType::try_from_idx(self, func_idx);

        let new_arr = ContextVar {
            loc: Some(loc),
            name: format!("tmp_arr{}", ctx.new_tmp(self).into_expr_err(loc)?),
            display_name: "arr".to_string(),
            storage: None,
            is_tmp: true,
            is_symbolic: false,
            is_return: false,
            tmp_of: None,
            dep_on: None,
            ty: ty.expect("No type for node"),
        };

        let arr = ContextVarNode::from(self.add_node(Node::ContextVar(new_arr)));

        let len_var = ContextVar {
            loc: Some(loc),
            name: arr.name(self).into_expr_err(loc)? + ".length",
            display_name: arr.display_name(self).unwrap() + ".length",
            storage: None,
            is_tmp: true,
            tmp_of: None,
            dep_on: None,
            is_symbolic: true,
            is_return: false,
            ty: ContextVarNode::from(len_cvar)
                .underlying(self)
                .into_expr_err(loc)?
                .ty
                .clone(),
        };

        let len_cvar = self.add_node(Node::ContextVar(len_var));
        self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(arr, self).into_expr_err(loc)?;
        self.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(len_cvar.into(), self).into_expr_err(loc)?;
        self.add_edge(
            len_cvar,
            arr,
            Edge::Context(ContextEdge::AttrAccess("length")),
        );

        // update the length
        if let Some(r) = arr.ref_range(self).into_expr_err(loc)? {
            let min = r.evaled_range_min(self, arena).into_expr_err(loc)?;
            let max = r.evaled_range_max(self, arena).into_expr_err(loc)?;

            if let Some(mut rd) = min.maybe_range_dyn() {
                rd.len = Box::new(Elem::from(len_cvar));
                arr.set_range_min(self, arena, Elem::ConcreteDyn(rd))
                    .into_expr_err(loc)?;
            }

            if let Some(mut rd) = max.maybe_range_dyn() {
                rd.len = Box::new(Elem::from(len_cvar));
                arr.set_range_min(self, arena, Elem::ConcreteDyn(rd))
                    .into_expr_err(loc)?;
            }
        }

        ctx.push_expr(ExprRet::Single(arr.into()), self)
            .into_expr_err(loc)
    }

    /// Construct a contract
    fn construct_contract(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        // construct a new contract
        if !input_exprs.is_empty() {
            self.parse_ctx_expr(arena, &input_exprs.unnamed_args().unwrap()[0], ctx)?;
        }
        self.apply_to_edges(ctx, loc, arena, &|analyzer, _arena, ctx, loc| {
            if !input_exprs.is_empty() {
                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                    return Err(ExprErr::NoRhs(loc, "Contract creation failed".to_string()));
                };
                if matches!(ret, ExprRet::CtxKilled(_)) {
                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                    return Ok(());
                }
            }

            let var = match ContextVar::maybe_from_user_ty(analyzer, loc, func_idx) {
                Some(v) => v,
                None => {
                    return Err(ExprErr::VarBadType(
                        loc,
                        format!(
                            "Could not create context variable from user type: {:?}",
                            analyzer.node(func_idx)
                        ),
                    ))
                }
            };
            // let idx = ret.expect_single().into_expr_err(loc)?;
            let contract_cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
            // contract_cvar
            //     .set_range_min(analyzer, Elem::from(idx))
            //     .into_expr_err(loc)?;
            // contract_cvar
            //     .set_range_max(analyzer, Elem::from(idx))
            //     .into_expr_err(loc)?;
            ctx.push_expr(ExprRet::Single(contract_cvar.into()), analyzer)
                .into_expr_err(loc)
        })
    }

    fn construct_struct_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        strukt: StructNode,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        let var = ContextVar::new_from_struct(loc, strukt, ctx, self).into_expr_err(loc)?;
        let cvar = self.add_node(Node::ContextVar(var));
        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
        let inputs = inputs.as_vec();
        // set struct fields
        strukt
            .fields(self)
            .iter()
            .zip(inputs)
            .try_for_each(|(field, input)| {
                let field_cvar = ContextVar::maybe_new_from_field(
                    self,
                    loc,
                    ContextVarNode::from(cvar)
                        .underlying(self)
                        .into_expr_err(loc)?,
                    field.underlying(self).unwrap().clone(),
                )
                .expect("Invalid struct field");

                let fc_node = self.add_node(Node::ContextVar(field_cvar));
                self.add_edge(
                    fc_node,
                    cvar,
                    Edge::Context(ContextEdge::AttrAccess("field")),
                );
                self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.add_var(fc_node.into(), self).into_expr_err(loc)?;
                let field_as_ret = ExprRet::Single(fc_node);
                self.match_assign_sides(arena, ctx, loc, &field_as_ret, &input)?;
                let _ = ctx.pop_expr_latest(loc, self).into_expr_err(loc)?;
                Ok(())
            })?;

        ctx.push_expr(ExprRet::Single(cvar), self)
            .into_expr_err(loc)
    }

    /// Construct a struct
    fn construct_struct(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        func_idx: NodeIdx,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        input_exprs.parse(arena, self, ctx, loc)?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(
                    loc,
                    "Struct construction call failed".to_string(),
                ));
            };

            analyzer.construct_struct_inner(arena, ctx, StructNode::from(func_idx), inputs, loc)
        })
    }
}
