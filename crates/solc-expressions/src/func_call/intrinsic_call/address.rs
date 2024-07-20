use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> AddressCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling address-based intrinsic functions
pub trait AddressCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform an `address.<..>` function call
    fn address_call(&mut self, ctx: ContextNode, func_name: &str, loc: Loc) -> Result<(), ExprErr> {
        match func_name {
            "delegatecall" | "staticcall" | "call" => self.external_call(ctx, func_name, loc),
            "send" => {
                let bn = self.builtin_or_add(Builtin::Bool);
                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                let node = self.add_node(cvar);
                ctx.add_var(node.into(), self).into_expr_err(loc)?;
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            }
            "transfer" => {
                // TODO: handle balance stuff. but otherwise, transfer does not
                // produce a return value.
                Ok(())
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find builtin address function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }

    fn external_call(&mut self, ctx: ContextNode, _ty: &str, loc: Loc) -> Result<(), ExprErr> {
        // TODO: Check if we have the code for the address
        // if we dont, model it as a unrestricted call that can make other calls
        ctx.pop_expr_latest(loc, self).into_expr_err(loc)?;
        // TODO: try to be smarter based on the address input
        let booln = self.builtin_or_add(Builtin::Bool);
        let bool_cvar = ContextVar::new_from_builtin(loc, booln.into(), self).into_expr_err(loc)?;
        let bool_node = self.add_node(bool_cvar);
        ctx.add_var(bool_node.into(), self).into_expr_err(loc)?;
        self.add_edge(bool_node, ctx, Edge::Context(ContextEdge::Variable));

        let bn = self.builtin_or_add(Builtin::DynamicBytes);
        let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
        let node = self.add_node(cvar);
        ctx.add_var(node.into(), self).into_expr_err(loc)?;
        self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(
            ExprRet::Multi(vec![ExprRet::Single(bool_node), ExprRet::Single(node)]),
            self,
        )
        .into_expr_err(loc)?;
        Ok(())
    }
}
