use crate::{
    range::Op, AnalyzerLike, BuiltInNode, Builtin, ContextBuilder, ContextNode, ContextVar,
    ContextVarNode, Node, NodeIdx, TmpConstruction, VarType,
};

use solang_parser::pt::{Expression, Loc};

impl<T> Cmp for T where T: AnalyzerLike + Sized {}
pub trait Cmp: AnalyzerLike + Sized {
    fn cmp(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        op: Op,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Vec<NodeIdx> {
        let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(&lhs_expr, ctx)[0]);
        let rhs_cvar = ContextVarNode::from(self.parse_ctx_expr(rhs_expr, ctx)[0]);
        let out_var = ContextVar {
            loc: Some(loc),
            name: format!(
                "tmp{}({} {} {})",
                lhs_cvar.name(self),
                op.to_string(),
                rhs_cvar.name(self),
                ctx.new_tmp(self)
            ),
            display_name: format!(
                "{} {} {}",
                lhs_cvar.display_name(self),
                op.to_string(),
                rhs_cvar.display_name(self),
            ),
            storage: None,
            tmp_of: Some(TmpConstruction::new(lhs_cvar, op, rhs_cvar)),
            ty: VarType::BuiltIn(BuiltInNode::from(self.builtin_or_add(Builtin::Bool)), None),
        };

        vec![self.add_node(Node::ContextVar(out_var))]
    }
}
