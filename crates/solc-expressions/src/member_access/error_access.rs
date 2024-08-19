use crate::LibraryAccess;

use graph::{
    nodes::{ContextNode, ContextVar, ContextVarNode, ErrorNode, ExprRet, Fielded},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> ErrorAccess for T where
    T: LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
}
/// Trait for performing member accesses on Structs
pub trait ErrorAccess:
    LibraryAccess + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    /// Perform member access on a error
    fn error_var_member_access(
        &mut self,
        cvar: ContextVarNode,
        err_node: ErrorNode,
        field_name: &str,
        loc: Loc,
    ) -> Result<(ExprRet, bool), ExprErr> {
        let cvar_name = cvar.name(self).unwrap();
        let name = format!("{cvar_name}.{field_name}");
        tracing::trace!("Error member access: {cvar_name}.{field_name}");

        if let Some(field) = cvar.field_of_fielded(field_name, self).into_expr_err(loc)? {
            return Ok((ExprRet::Single(field.into()), false));
        }

        if let Some(field) = err_node.find_field(self, field_name) {
            if let Some(field_cvar) = ContextVar::maybe_new_from_error_param(
                self,
                loc,
                cvar.underlying(self).unwrap(),
                field.underlying(self).unwrap().clone(),
                0,
            ) {
                let fc_node = self.add_node(field_cvar);
                self.add_edge(
                    fc_node,
                    cvar.first_version(self),
                    Edge::Context(ContextEdge::AttrAccess("field")),
                );
                Ok((ExprRet::Single(fc_node), false))
            } else {
                panic!("Couldn't create field variable");
            }
        } else {
            Err(ExprErr::MemberAccessNotFound(
                loc,
                format!(
                    "Unknown member access \"{name}\" on error \"{}\"",
                    err_node.name(self).into_expr_err(loc)?
                ),
            ))
        }
    }
}
