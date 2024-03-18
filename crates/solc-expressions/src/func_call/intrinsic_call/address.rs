use crate::func_caller::NamedOrUnnamedArgs;
use crate::{ExprErr, IntoExprErr};

use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> AddressCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling address-based intrinsic functions
pub trait AddressCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform an `address.<..>` function call
    fn address_call(
        &mut self,
        func_name: String,
        _input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "delegatecall" | "staticcall" | "call" => self.external_call(&func_name, loc, ctx),
            "code" => {
                // TODO: try to be smarter based on the address input
                let bn = self.builtin_or_add(Builtin::DynamicBytes);
                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                let node = self.add_node(Node::ContextVar(cvar));
                ctx.add_var(node.into(), self).into_expr_err(loc)?;
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "balance" => {
                // TODO: try to be smarter based on the address input
                let bn = self.builtin_or_add(Builtin::Uint(256));
                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                let node = self.add_node(Node::ContextVar(cvar));
                ctx.add_var(node.into(), self).into_expr_err(loc)?;
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
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

    fn external_call(&mut self, _ty: &str, loc: Loc, ctx: ContextNode) -> Result<(), ExprErr> {
        // TODO: Check if we have the code for the address
        // if we dont, model it as a unrestricted call that can make other calls
        ctx.pop_expr_latest(loc, self).into_expr_err(loc)?;
        // TODO: try to be smarter based on the address input
        let booln = self.builtin_or_add(Builtin::Bool);
        let bool_cvar = ContextVar::new_from_builtin(loc, booln.into(), self).into_expr_err(loc)?;
        let bool_node = self.add_node(Node::ContextVar(bool_cvar));
        ctx.add_var(bool_node.into(), self).into_expr_err(loc)?;
        self.add_edge(bool_node, ctx, Edge::Context(ContextEdge::Variable));

        let bn = self.builtin_or_add(Builtin::DynamicBytes);
        let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
        let node = self.add_node(Node::ContextVar(cvar));
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
