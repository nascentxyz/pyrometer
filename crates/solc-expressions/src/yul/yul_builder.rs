//! Trait and blanket implementation for parsing yul-based statements and expressions

use graph::{
    nodes::{BuiltInNode, Builtin, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, SolcRange, VarType,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> YulBuilder for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Trait that processes Yul statements and expressions
pub trait YulBuilder: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Match [`ExprRet`] from the sides of an `YulAssign` to perform the assignment
    fn match_assign_yul(
        &mut self,
        _ctx: ContextNode,
        loc: Loc,
        nodes: &[ContextVarNode],
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            s @ ExprRet::Single(_) | s @ ExprRet::SingleLiteral(_) => {
                self.match_assign_yul_inner(loc, &nodes[0], s)?;
            }
            ExprRet::Multi(inner) => {
                if inner.len() == nodes.len() {
                    inner
                        .into_iter()
                        .zip(nodes.iter())
                        .map(|(ret, node)| self.match_assign_yul_inner(loc, node, ret))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                } else {
                    return Err(ExprErr::Todo(
                        loc,
                        format!("Differing number of assignees and assignors in yul expression, assignors: {}, assignees: {}", nodes.len(), inner.len()),
                    ));
                };
            }
            ExprRet::CtxKilled(_kind) => {}
            ExprRet::Null => {}
        }

        Ok(())
    }

    /// Perform the actual yul assignment
    fn match_assign_yul_inner(
        &mut self,
        loc: Loc,
        node: &ContextVarNode,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret.flatten() {
            ExprRet::Single(idx) | ExprRet::SingleLiteral(idx) => {
                let assign = ContextVarNode::from(idx);
                let assign_ty = assign.underlying(self).into_expr_err(loc)?.ty.clone();
                if assign_ty.is_dyn(self).into_expr_err(loc)? {
                    let b_ty = self.builtin_or_add(Builtin::Bytes(32));
                    node.underlying_mut(self).into_expr_err(loc)?.ty =
                        VarType::try_from_idx(self, b_ty).unwrap();
                } else {
                    node.underlying_mut(self).into_expr_err(loc)?.ty = assign_ty;
                }
            }
            ExprRet::Multi(_inner) => {
                return Err(ExprErr::Todo(
                    loc,
                    "Multi in single assignment yul expression is unhandled".to_string(),
                ))
            }
            ExprRet::CtxKilled(..) => {}
            ExprRet::Null => {}
        }
        Ok(())
    }

    fn slot(&mut self, ctx: ContextNode, loc: Loc, lhs: ContextVarNode) -> ContextVarNode {
        let lhs = lhs.first_version(self);
        let name = format!("{}.slot", lhs.name(self).unwrap());
        tracing::trace!("Slot access: {}", name);
        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).unwrap() {
            attr_var.latest_version_or_inherited_in_ctx(ctx, self)
        } else {
            let slot_var = ContextVar {
                loc: Some(loc),
                name: lhs.name(self).unwrap() + ".slot",
                display_name: lhs.display_name(self).unwrap() + ".slot",
                storage: None,
                is_tmp: false,
                tmp_of: None,
                dep_on: None,
                is_symbolic: true,
                is_return: false,
                is_fundamental: None,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    SolcRange::try_from_builtin(&Builtin::Uint(256)),
                ),
            };
            let slot_node = self.add_node(slot_var);

            self.add_edge(slot_node, lhs, Edge::Context(ContextEdge::SlotAccess));
            self.add_edge(slot_node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.add_var(slot_node.into(), self).unwrap();
            slot_node.into()
        }
    }
}
