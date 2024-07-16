use crate::func_call::helper::CallerHelper;
use graph::nodes::SubContextKind;

use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, Context, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc};

impl<T> PrecompileCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
}

/// Trait for calling precompile intrinsic functions, like `ecrecover`
pub trait PrecompileCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + CallerHelper
{
    /// Perform a precompile's function call, like `ecrecover`
    fn precompile_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "sha256" => {
                // TODO: Compile time calculate the hash if we have concretes.
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Bytes(32)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "ripemd160" => {
                // TODO: Compile time calculate the hash if we have concretes.
                let var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Bytes(32)).into(),
                    self,
                )
                .into_expr_err(loc)?;
                let cvar = self.add_node(var);
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            "ecrecover" => {
                let func_idx = *(self.builtin_fn_nodes().get("ecrecover").unwrap());
                let subctx_kind = SubContextKind::new_fn_call(ctx, None, func_idx.into(), true);
                let cctx = Context::new_subctx(subctx_kind, loc, self, None).into_expr_err(loc)?;
                let call_ctx = self.add_node(Node::Context(cctx));
                ctx.set_child_call(call_ctx.into(), self)
                    .into_expr_err(loc)?;
                let call_node = self.add_node(Node::FunctionCall);
                self.add_edge(call_node, func_idx, Edge::Context(ContextEdge::Call));
                self.add_edge(call_node, ctx, Edge::Context(ContextEdge::Subcontext));
                self.add_edge(call_ctx, call_node, Edge::Context(ContextEdge::Subcontext));

                let mut inner_vals = vec![];
                match inputs {
                    ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                        inner_vals.push(ContextVarNode::from(var).display_name(self).unwrap());
                    }
                    _ => inner_vals.push("<unknown>".to_string()),
                }
                let inner_name = inner_vals.into_iter().collect::<Vec<_>>().join(", ");
                let mut var = ContextVar::new_from_builtin(
                    loc,
                    self.builtin_or_add(Builtin::Address).into(),
                    self,
                )
                .into_expr_err(loc)?;
                var.display_name = format!("ecrecover({})", inner_name);
                var.is_symbolic = true;
                var.is_return = true;
                let cvar = self.add_node(var);
                ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
                self.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Return));
                ContextNode::from(call_ctx)
                    .add_return_node(loc, cvar.into(), self)
                    .into_expr_err(loc)?;

                let subctx_kind = SubContextKind::new_fn_ret(call_ctx.into(), ctx);
                let rctx = Context::new_subctx(subctx_kind, loc, self, None).into_expr_err(loc)?;
                let ret_ctx = self.add_node(Node::Context(rctx));
                ContextNode::from(call_ctx)
                    .set_child_call(ret_ctx.into(), self)
                    .into_expr_err(loc)?;

                let tmp_ret = ContextVarNode::from(cvar)
                    .as_tmp(
                        ContextNode::from(call_ctx).underlying(self).unwrap().loc,
                        ret_ctx.into(),
                        self,
                    )
                    .unwrap();
                tmp_ret.underlying_mut(self).unwrap().is_return = true;
                tmp_ret.underlying_mut(self).unwrap().display_name =
                    format!("ecrecover({}).return", inner_name);
                ctx.add_var(tmp_ret, self).into_expr_err(loc)?;
                self.add_edge(tmp_ret, ret_ctx, Edge::Context(ContextEdge::Variable));

                ContextNode::from(ret_ctx)
                    .push_expr(ExprRet::Single(tmp_ret.into()), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find precompile function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
