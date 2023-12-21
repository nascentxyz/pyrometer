use crate::func_caller::NamedOrUnnamedArgs;
use crate::{ContextBuilder, ExprErr, ExpressionParser, IntoExprErr};

use graph::{
    nodes::{Builtin, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node,
};

use solang_parser::pt::{Expression, Loc};

impl<T> AbiCaller for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for calling abi-namespaced intrinsic functions
pub trait AbiCaller: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Perform an `abi.<..>` function call
    fn abi_call(
        &mut self,
        func_name: String,
        input_exprs: &NamedOrUnnamedArgs,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match &*func_name {
            "abi.decode" => {
                // we skip the first because that is what is being decoded.
                // TODO: check if we have a concrete bytes value
                fn match_decode(
                    ctx: ContextNode,
                    loc: &Loc,
                    ret: ExprRet,
                    analyzer: &mut impl AnalyzerBackend,
                ) -> Result<(), ExprErr> {
                    match ret {
                        ExprRet::Single(ty) => match analyzer.node(ty) {
                            Node::Builtin(_) => {
                                let var = ContextVar::new_from_builtin(*loc, ty.into(), analyzer)
                                    .into_expr_err(*loc)?;
                                let node = analyzer.add_node(Node::ContextVar(var));
                                ctx.add_var(node.into(), analyzer).into_expr_err(*loc)?;
                                analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                    .into_expr_err(*loc)?;
                                Ok(())
                            }
                            Node::ContextVar(cvar) => {
                                let bn = analyzer
                                    .builtin_or_add(
                                        cvar.ty.as_builtin(analyzer).into_expr_err(*loc)?,
                                    )
                                    .into();
                                let var = ContextVar::new_from_builtin(*loc, bn, analyzer)
                                    .into_expr_err(*loc)?;
                                let node = analyzer.add_node(Node::ContextVar(var));
                                ctx.add_var(node.into(), analyzer).into_expr_err(*loc)?;
                                analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                    .into_expr_err(*loc)?;
                                Ok(())
                            }
                            Node::Struct(_) => {
                                let var =
                                    ContextVar::new_from_struct(*loc, ty.into(), ctx, analyzer)
                                        .into_expr_err(*loc)?;
                                let node = analyzer.add_node(Node::ContextVar(var));
                                ctx.add_var(node.into(), analyzer).into_expr_err(*loc)?;
                                analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                    .into_expr_err(*loc)?;
                                Ok(())
                            }
                            Node::Contract(_) => {
                                let var = ContextVar::new_from_contract(*loc, ty.into(), analyzer)
                                    .into_expr_err(*loc)?;
                                let node = analyzer.add_node(Node::ContextVar(var));
                                ctx.add_var(node.into(), analyzer).into_expr_err(*loc)?;
                                analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                    .into_expr_err(*loc)?;
                                Ok(())
                            }
                            e => todo!("Unhandled type in abi.decode: {e:?}"),
                        },
                        ExprRet::Multi(inner) => inner
                            .iter()
                            .try_for_each(|i| match_decode(ctx, loc, i.clone(), analyzer)),
                        ExprRet::CtxKilled(kind) => {
                            ctx.kill(analyzer, *loc, kind).into_expr_err(*loc)
                        }
                        e => panic!("This is invalid solidity: {:?}", e),
                    }
                }
                let input_exprs = input_exprs.unnamed_args().unwrap();
                self.parse_ctx_expr(&input_exprs[1], ctx)?;
                self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "abi.decode was not given the types for decoding".to_string(),
                        ));
                    };
                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    match_decode(ctx, &loc, ret, analyzer)
                })
            }
            "abi.encode"
            | "abi.encodePacked"
            | "abi.encodeCall"
            | "abi.encodeWithSignature"
            | "abi.encodeWithSelector" => {
                // TODO: Support concrete abi encoding
                let bn = self.builtin_or_add(Builtin::DynamicBytes);
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
                    "Could not find abi function: \"{func_name}\", context: {}",
                    ctx.path(self),
                ),
            )),
        }
    }
}
