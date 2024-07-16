use graph::{
    elem::Elem,
    nodes::{Concrete, ContextNode, ContextVar, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};
use shared::{ExprErr, FlatExpr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc, Parameter, ParameterList};

impl<T> List for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Dealing with list parsing and operations
pub trait List: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    fn list(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        params: &ParameterList,
    ) -> Result<(), ExprErr> {
        unreachable!("Should not have called this");
    }

    fn match_input_ty(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        ty_ret: &ExprRet,
        input: &Parameter,
    ) -> Result<ExprRet, ExprErr> {
        match ty_ret {
            ExprRet::Null => Ok(ExprRet::Null),
            ExprRet::Single(ty) | ExprRet::SingleLiteral(ty) => {
                if let Some(input_name) = &input.name {
                    let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                    let var = ContextVar {
                        loc: Some(*loc),
                        name: input_name.to_string(),
                        display_name: input_name.to_string(),
                        storage: input.storage.as_ref().map(|s| s.clone().into()),
                        is_tmp: false,
                        is_symbolic: false,
                        tmp_of: None,
                        dep_on: None,
                        is_return: false,
                        ty,
                    };
                    let input_node = self.add_node(Node::ContextVar(var));
                    ctx.add_var(input_node.into(), self).into_expr_err(*loc)?;
                    self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(input_node))
                } else {
                    match self.node(*ty) {
                        Node::ContextVar(_var) => {
                            // reference the variable directly, don't create a temporary variable
                            Ok(ExprRet::Single(*ty))
                        }
                        _ => {
                            // create a tmp
                            let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                            let tmp_num = ctx.new_tmp(self).into_expr_err(*loc)?;
                            let new_lhs_underlying = ContextVar {
                                loc: Some(*loc),
                                name: format!("tmp{tmp_num}"),
                                display_name: format!("tmp{tmp_num}"),
                                storage: input.storage.as_ref().map(|s| s.clone().into()),
                                is_tmp: true,
                                is_symbolic: false,
                                tmp_of: None,
                                dep_on: None,
                                is_return: false,
                                ty,
                            };
                            let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
                            ctx.add_var(input_node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(input_node))
                        }
                    }
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .iter()
                    .map(|i| self.match_input_ty(ctx, loc, i, input))
                    .collect::<Result<_, _>>()?,
            )),
            ExprRet::CtxKilled(kind) => Ok(ExprRet::CtxKilled(*kind)),
        }
    }

    fn list_inner(
        &mut self,
        ctx: ContextNode,
        param: FlatExpr,
        ret: ExprRet,
        loc: Loc,
    ) -> Result<ExprRet, ExprErr> {
        match ret {
            ExprRet::Null => Ok(ExprRet::Null),
            ExprRet::Single(ty) | ExprRet::SingleLiteral(ty) => {
                println!("param: {:#?}", param);
                let FlatExpr::Parameter(_, maybe_storage, maybe_name) = param else {
                    unreachable!()
                };

                if let Some(input_name) = &maybe_name {
                    let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                    let var = ContextVar {
                        loc: Some(loc),
                        name: input_name.to_string(),
                        display_name: input_name.to_string(),
                        storage: maybe_storage,
                        is_tmp: false,
                        is_symbolic: false,
                        tmp_of: None,
                        dep_on: None,
                        is_return: false,
                        ty,
                    };
                    let input_node = self.add_node(Node::ContextVar(var));
                    ctx.add_var(input_node.into(), self).into_expr_err(loc)?;
                    self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                    Ok(ExprRet::Single(input_node))
                } else {
                    match self.node(ty) {
                        Node::ContextVar(_var) => {
                            // reference the variable directly, don't create a temporary variable
                            Ok(ExprRet::Single(ty))
                        }
                        _ => {
                            // create a tmp
                            let ty = VarType::try_from_idx(self, ty).expect("Not a known type");
                            let tmp_num = ctx.new_tmp(self).into_expr_err(loc)?;
                            let new_lhs_underlying = ContextVar {
                                loc: Some(loc),
                                name: format!("tmp{tmp_num}"),
                                display_name: format!("tmp{tmp_num}"),
                                storage: maybe_storage,
                                is_tmp: true,
                                is_symbolic: false,
                                tmp_of: None,
                                dep_on: None,
                                is_return: false,
                                ty,
                            };
                            let input_node = self.add_node(Node::ContextVar(new_lhs_underlying));
                            ctx.add_var(input_node.into(), self).into_expr_err(loc)?;
                            self.add_edge(input_node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single(input_node))
                        }
                    }
                }
            }
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .into_iter()
                    .map(|i| self.list_inner(ctx, param, i, loc))
                    .collect::<Result<_, _>>()?,
            )),
            ExprRet::CtxKilled(kind) => Ok(ExprRet::CtxKilled(kind)),
        }
    }
}
