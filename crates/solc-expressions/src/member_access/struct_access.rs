use crate::{ExprErr, IntoExprErr, LibraryAccess};

use graph::{
    nodes::{ContextNode, ContextVar, ContextVarNode, ExprRet, StructNode},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> StructAccess for T where
    T: LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}
/// Trait for performing member accesses on Structs
pub trait StructAccess:
    LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Perform member access on a struct
    fn struct_member_access(
        &mut self,
        member_idx: NodeIdx,
        struct_node: StructNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
        maybe_parent: Option<ContextVar>,
    ) -> Result<ExprRet, ExprErr> {
        let name = format!(
            "{}.{}",
            struct_node.name(self).into_expr_err(loc)?,
            ident.name
        );
        tracing::trace!("Struct member access: {}", name);
        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
            Ok(ExprRet::Single(attr_var.latest_version(self).into()))
        } else if let Some(field) = struct_node.find_field(self, ident) {
            let cvar = if let Some(parent) = maybe_parent {
                parent
            } else {
                ContextVar::maybe_from_user_ty(self, loc, struct_node.into()).unwrap()
            };
            if let Some(field_cvar) = ContextVar::maybe_new_from_field(
                self,
                loc,
                &cvar,
                field.underlying(self).unwrap().clone(),
            ) {
                let fc_node = self.add_node(Node::ContextVar(field_cvar));
                self.add_edge(
                    fc_node,
                    ContextVarNode::from(member_idx).first_version(self),
                    Edge::Context(ContextEdge::AttrAccess),
                );
                ctx.add_var(fc_node.into(), self).into_expr_err(loc)?;
                self.add_edge(fc_node, ctx, Edge::Context(ContextEdge::Variable));
                Ok(ExprRet::Single(fc_node))
            } else {
                panic!("Couldn't create field variable");
            }
        } else if let Some(func) = self.library_func_search(ctx, struct_node.0.into(), ident) {
            Ok(func)
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on struct \"{}\"",
                    ident.name,
                    struct_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }
}
