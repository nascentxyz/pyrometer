use crate::LibraryAccess;

use graph::{
    nodes::{ContextNode, ContextVar, EnumNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::{ExprErr, IntoExprErr, NodeIdx};

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> EnumAccess for T where
    T: LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}

/// Trait for performing member access on an enum
pub trait EnumAccess:
    LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Perform member access on an enum
    fn enum_member_access(
        &mut self,
        _member_idx: NodeIdx,
        enum_node: EnumNode,
        ident: &Identifier,
        ctx: ContextNode,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!("Enum member access: {}", ident.name);

        if let Some(variant) = enum_node
            .variants(self)
            .into_expr_err(loc)?
            .iter()
            .find(|variant| **variant == ident.name)
        {
            let var =
                ContextVar::new_from_enum_variant(self, ctx, loc, enum_node, variant.to_string())
                    .into_expr_err(loc)?;
            let cvar = self.add_node(var);
            ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
            self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
            Ok(ExprRet::Single(cvar))
        } else if let Some(ret) = self.library_func_search(ctx, enum_node.0.into(), ident) {
            Ok(ret)
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{}\" on enum \"{}\"",
                    ident.name,
                    enum_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }
}
