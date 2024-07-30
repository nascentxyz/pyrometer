use crate::variable::Variable;
use crate::{assign::Assign, func_call::helper::CallerHelper};
use graph::nodes::Builtin;

use graph::{
    elem::*,
    nodes::{Concrete, ContextNode, ContextVar, ContextVarNode, ContractNode, ExprRet, StructNode},
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
            display_name: "tmp_arr".to_string(),
            storage: None,
            is_tmp: true,
            is_symbolic: false,
            is_return: false,
            tmp_of: None,
            dep_on: None,
            ty: ty.expect("No type for node"),
        };

        let arr = ContextVarNode::from(self.add_node(new_arr));

        let u256 = self.builtin_or_add(Builtin::Uint(256));
        let new_len_var = ContextVar {
            loc: Some(loc),
            name: arr.name(self).into_expr_err(loc)? + ".length",
            display_name: arr.display_name(self).unwrap() + ".length",
            storage: None,
            is_tmp: true,
            tmp_of: None,
            dep_on: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::try_from_idx(self, u256).unwrap(),
        };

        let new_len_cvar = ContextVarNode::from(self.add_node(new_len_var));
        self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(arr, self).into_expr_err(loc)?;
        self.add_edge(new_len_cvar, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(new_len_cvar, self).into_expr_err(loc)?;
        self.add_edge(
            new_len_cvar,
            arr,
            Edge::Context(ContextEdge::AttrAccess("length")),
        );

        self.assign(arena, loc, new_len_cvar, len_cvar.into(), ctx)?;

        ctx.push_expr(ExprRet::Single(arr.into()), self)
            .into_expr_err(loc)
    }

    /// Construct a contract
    fn construct_contract_inner(
        &mut self,
        _arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        con_node: ContractNode,
        _input: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        // construct a new contract
        let var = match ContextVar::maybe_from_user_ty(self, loc, con_node.0.into()) {
            Some(v) => v,
            None => {
                return Err(ExprErr::VarBadType(
                    loc,
                    format!(
                        "Could not create context variable from user type: {:?}",
                        self.node(con_node)
                    ),
                ))
            }
        };
        let contract_cvar = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
        ctx.push_expr(ExprRet::Single(contract_cvar.into()), self)
            .into_expr_err(loc)
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
        let cvar = self.add_node(var);
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

                let fc_node = self.add_node(field_cvar);
                self.add_edge(
                    fc_node,
                    cvar,
                    Edge::Context(ContextEdge::AttrAccess("field")),
                );
                self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.add_var(fc_node.into(), self).into_expr_err(loc)?;
                let field_as_ret = ExprRet::Single(fc_node);
                self.match_assign_sides(arena, ctx, loc, &field_as_ret, &input)?;
                let _ = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                Ok(())
            })?;

        ctx.push_expr(ExprRet::Single(cvar), self)
            .into_expr_err(loc)
    }
}
