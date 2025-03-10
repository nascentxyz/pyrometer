use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::{ExprErr, IntoExprErr};

use solang_parser::pt::{Expression, Loc};

impl<T> AbiCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling abi-namespaced intrinsic functions
pub trait AbiCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    fn abi_decode(&mut self, ctx: ContextNode, inputs: ExprRet, loc: Loc) -> Result<(), ExprErr> {
        match inputs {
            ExprRet::Single(ty) => match self.node(ty) {
                Node::Builtin(_) => {
                    let var =
                        ContextVar::new_from_builtin(loc, ty.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(var);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.push_expr(ExprRet::Single(node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                Node::ContextVar(cvar) => {
                    let bn = self
                        .builtin_or_add(cvar.ty.as_builtin(self).into_expr_err(loc)?)
                        .into();
                    let var = ContextVar::new_from_builtin(loc, bn, self).into_expr_err(loc)?;
                    let node = self.add_node(var);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.push_expr(ExprRet::Single(node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                Node::Struct(_) => {
                    let var = ContextVar::new_from_struct(loc, ty.into(), ctx, self)
                        .into_expr_err(loc)?;
                    let node = self.add_node(var);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.push_expr(ExprRet::Single(node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                Node::Contract(_) => {
                    let var =
                        ContextVar::new_from_contract(loc, ty.into(), self).into_expr_err(loc)?;
                    let node = self.add_node(var);
                    ctx.add_var(node.into(), self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.push_expr(ExprRet::Single(node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                e => todo!("Unhandled type in abi.decode: {e:?}"),
            },
            ExprRet::Multi(inner) => inner
                .iter()
                .try_for_each(|i| self.abi_decode(ctx, i.clone(), loc)),
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            e => panic!("This is invalid solidity: {:?}", e),
        }
    }

    fn abi_call_inner(
        &mut self,
        ctx: ContextNode,
        func_name: &str,
        inputs: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match func_name {
            "abi.decode" => {
                // we skip the first because that is what is being decoded.
                // TODO: check if we have a concrete bytes value
                let decode_as = ExprRet::Multi(inputs.as_vec()[1..].to_vec());
                self.abi_decode(ctx, decode_as, loc)
            }
            "abi.encode"
            | "abi.encodePacked"
            | "abi.encodeCall"
            | "abi.encodeWithSignature"
            | "abi.encodeWithSelector" => {
                // TODO: Support concrete abi encoding
                let bn = self.builtin_or_add(Builtin::DynamicBytes);
                let cvar = ContextVar::new_from_builtin(loc, bn.into(), self).into_expr_err(loc)?;
                let node = self.add_node(cvar);
                ctx.add_var(node.into(), self).into_expr_err(loc)?;
                self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            _ => Err(ExprErr::FunctionNotFound(
                loc,
                format!(
                    "Could not find abi function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
