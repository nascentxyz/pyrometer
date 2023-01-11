use crate::AnalyzerLike;
use crate::{
    range::{Op, Range, RangeElem},
    ContextBuilder, ContextEdge, ContextNode, ContextVar, ContextVarNode, Edge, Node, NodeIdx,
    TmpConstruction,
};
use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> BinOp for T where T: AnalyzerLike + Sized {}
pub trait BinOp: AnalyzerLike + Sized {
    fn op_expr(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
        op: Op,
        assign: bool,
    ) -> Vec<NodeIdx> {
        let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(&lhs_expr, ctx)[0]);
        let rhs_cvar = ContextVarNode::from(self.parse_ctx_expr(rhs_expr, ctx)[0]);
        self.op(loc, lhs_cvar, rhs_cvar, ctx, op, assign)
    }

    fn op(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
        op: Op,
        assign: bool,
    ) -> Vec<NodeIdx> {
        let new_lhs = if assign {
            self.advance_var(lhs_cvar, loc)
        } else {
            let mut new_lhs_underlying = ContextVar {
                loc: Some(loc),
                name: format!(
                    "tmp{}({} {} {})",
                    ctx.new_tmp(self),
                    lhs_cvar.name(self),
                    op.to_string(),
                    rhs_cvar.name(self)
                ),
                display_name: format!(
                    "({} {} {})",
                    lhs_cvar.display_name(self),
                    op.to_string(),
                    rhs_cvar.display_name(self)
                ),
                storage: None,
                tmp_of: Some(TmpConstruction::new(lhs_cvar, op, rhs_cvar)),
                ty: lhs_cvar.underlying(self).ty.clone(),
            };

            // will potentially mutate the ty from concrete to builtin with a concrete range
            new_lhs_underlying.ty.concrete_to_builtin(self);

            let new_var = self.add_node(Node::ContextVar(new_lhs_underlying));
            self.add_edge(new_var, ctx, Edge::Context(ContextEdge::Variable));
            ContextVarNode::from(new_var)
        };

        let lhs_range = if let Some(lhs_range) = new_lhs.range(self) {
            lhs_range
        } else {
            Range {
                min: RangeElem::Concrete(U256::zero(), Loc::Implicit),
                max: RangeElem::Concrete(U256::MAX, Loc::Implicit),
            }
        };

        let (func, range_sides) = Range::dyn_fn_from_op(op);
        let new_range = func(lhs_range, rhs_cvar, range_sides, loc);
        new_lhs.set_range_min(self, new_range.min);
        new_lhs.set_range_max(self, new_range.max);
        vec![new_lhs.into()]
    }
}
