use crate::LibraryAccess;

use graph::{
    nodes::{ContextNode, ContextVar, ContextVarNode, ExprRet, StructNode},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr, NodeIdx};

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
    fn struct_var_member_access(
        &mut self,
        ctx: ContextNode,
        cvar: ContextVarNode,
        struct_node: StructNode,
        field_name: &str,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        let cvar_name = cvar.name(self).unwrap();
        let name = format!("{cvar_name}.{field_name}");
        tracing::trace!("Struct member access: {cvar_name}.{field_name}");

        if let Some(field) = cvar.field_of_struct(field_name, self).into_expr_err(loc)? {
            return Ok(ExprRet::Single(field.into()));
        }

        if let Some(field) = struct_node.find_field(self, field_name) {
            if let Some(field_cvar) = ContextVar::maybe_new_from_field(
                self,
                loc,
                cvar.underlying(self).unwrap(),
                field.underlying(self).unwrap().clone(),
            ) {
                let fc_node = self.add_node(field_cvar);
                self.add_edge(
                    fc_node,
                    cvar.first_version(self),
                    Edge::Context(ContextEdge::AttrAccess("field")),
                );
                Ok(ExprRet::Single(fc_node))
            } else {
                panic!("Couldn't create field variable");
            }
        } else if let Some(func) = self.library_func_search(ctx, struct_node.0.into(), &name) {
            Ok(func)
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{name}\" on struct \"{}\"",
                    struct_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }
}
