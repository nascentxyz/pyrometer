use crate::context::exprs::IntoExprErr;
use crate::context::ContextBuilder;
use crate::context::ExprParser;
use crate::AnalyzerLike;
use crate::ExprErr;
use crate::ExprRet;
use shared::context::ContextVar;
use shared::context::ContextVarNode;
use shared::nodes::Builtin;
use shared::nodes::VarType;
use shared::{
    context::{ContextEdge, ContextNode},
    Edge, Node,
};
use solang_parser::helpers::CodeLocation;
use solang_parser::pt::Expression;
use solang_parser::pt::Loc;

use solang_parser::pt::{YulExpression, YulFor, YulStatement, YulSwitch};

mod yul_cond_op;
pub use yul_cond_op::*;

mod yul_funcs;
pub use yul_funcs::*;

impl<T> YulBuilder for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
}
pub trait YulBuilder:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + ExprParser
{
    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    fn parse_ctx_yul_statement(&mut self, stmt: &YulStatement, ctx: ContextNode)
    where
        Self: Sized,
    {
        if let Some(true) = self.add_if_err(ctx.is_ended(self).into_expr_err(stmt.loc())) {
            return;
        }
        if let Some(live_edges) = self.add_if_err(ctx.live_edges(self).into_expr_err(stmt.loc())) {
            if live_edges.is_empty() {
                self.parse_ctx_yul_stmt_inner(stmt, ctx)
            } else {
                live_edges.iter().for_each(|fork_ctx| {
                    self.parse_ctx_yul_stmt_inner(stmt, *fork_ctx);
                });
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_yul_stmt_inner(&mut self, stmt: &YulStatement, ctx: ContextNode)
    where
        Self: Sized,
    {
        use YulStatement::*;
        let forks = self
            .add_if_err(ctx.live_edges(self).into_expr_err(stmt.loc()))
            .unwrap();
        match stmt {
            Assign(_loc, yul_exprs, yul_expr) => {
                if forks.is_empty() {
                    let ret = yul_exprs
                        .iter()
                        .map(|expr| self.parse_ctx_yul_expr(expr, ctx))
                        .collect::<Result<Vec<ExprRet>, ExprErr>>();
                    if let Some(lhs_side) = self.add_if_err(ret) {
                        let ret = self.parse_ctx_yul_expr(yul_expr, ctx);
                        if let Some(rhs_side) = self.add_if_err(ret) {
                            let ret = self.match_assign_sides(
                                stmt.loc(),
                                &ExprRet::Multi(lhs_side),
                                &rhs_side,
                            );
                            let _ = self.add_if_err(ret);
                        }
                    }
                } else {
                    forks.into_iter().for_each(|ctx| {
                        let ret = yul_exprs
                            .iter()
                            .map(|expr| self.parse_ctx_yul_expr(expr, ctx))
                            .collect::<Result<Vec<ExprRet>, ExprErr>>();
                        if let Some(lhs_side) = self.add_if_err(ret) {
                            let ret = self.parse_ctx_yul_expr(yul_expr, ctx);
                            if let Some(rhs_side) = self.add_if_err(ret) {
                                let ret = self.match_assign_sides(
                                    stmt.loc(),
                                    &ExprRet::Multi(lhs_side),
                                    &rhs_side,
                                );
                                let _ = self.add_if_err(ret);
                            }
                        }
                    });
                }
            }
            VariableDeclaration(loc, yul_idents, maybe_yul_expr) => {
                let nodes = yul_idents
                    .iter()
                    .map(|ident| {
                        let b_ty = self.builtin_or_add(Builtin::Uint(256));
                        let var = ContextVar {
                            loc: Some(ident.loc),
                            name: ident.id.name.clone(),
                            display_name: ident.id.name.clone(),
                            storage: None,
                            is_tmp: false,
                            tmp_of: None,
                            is_symbolic: true,
                            is_return: false,
                            ty: VarType::try_from_idx(self, b_ty).unwrap(),
                        };
                        let cvar = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                        self.advance_var_in_ctx(cvar, *loc, ctx).unwrap()
                    })
                    .collect::<Vec<_>>();

                if let Some(yul_expr) = maybe_yul_expr {
                    let ret = self.parse_ctx_yul_expr(yul_expr, ctx);
                    if let Some(ret) = self.add_if_err(ret) {
                        let ret = self.match_assign_yul(*loc, &nodes, ret);
                        let _ = self.add_if_err(ret);
                    }
                }
            }
            If(loc, yul_expr, yul_block) => {
                if forks.is_empty() {
                    let ret = self.yul_cond_op_stmt(*loc, yul_expr, yul_block, ctx);
                    let _ = self.add_if_err(ret);
                } else {
                    forks.into_iter().for_each(|ctx| {
                        let ret = self.yul_cond_op_stmt(*loc, yul_expr, yul_block, ctx);
                        let _ = self.add_if_err(ret);
                    });
                }
            }
            For(YulFor {
                loc: _,
                init_block: _,
                condition: _,
                post_block: _,
                execution_block: _,
            }) => {
                todo!()
            }
            Switch(YulSwitch {
                loc: _,
                condition: _,
                cases: _,
                default: _,
            }) => {
                todo!()
            }
            Leave(_loc) => {
                todo!()
            }
            Break(_loc) => {
                todo!()
            }
            Continue(_loc) => {
                todo!()
            }
            Block(yul_block) => {
                yul_block
                    .statements
                    .iter()
                    .for_each(|stmt| self.parse_ctx_yul_stmt_inner(stmt, ctx));
            }
            FunctionDefinition(_yul_func_def) => {
                todo!()
            }
            FunctionCall(yul_func_call) => {
                let ret = self.yul_func_call(yul_func_call, ctx);
                let _ = self.add_if_err(ret);
            }
            Error(_loc) => {
                todo!()
            }
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_yul_expr(
        &mut self,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        tracing::trace!("Parsing yul expression: {expr:?}");
        if ctx.is_ended(self).into_expr_err(expr.loc())? {
            return Ok(ExprRet::CtxKilled);
        }

        if ctx.live_edges(self).into_expr_err(expr.loc())?.is_empty() {
            self.parse_ctx_yul_expr_inner(expr, ctx)
        } else {
            let rets: Vec<ExprRet> = ctx
                .live_edges(self)
                .into_expr_err(expr.loc())?
                .iter()
                .map(|fork_ctx| self.parse_ctx_yul_expr(expr, *fork_ctx))
                .collect::<Result<_, ExprErr>>()?;
            if rets.len() == 1 {
                Ok(rets.into_iter().take(1).next().unwrap())
            } else {
                Ok(ExprRet::Multi(rets))
            }
        }
    }

    fn parse_ctx_yul_expr_inner(
        &mut self,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        use YulExpression::*;
        match expr {
            BoolLiteral(loc, b, _) => self.bool_literal(ctx, *loc, *b),
            NumberLiteral(loc, int, expr, _unit) => {
                self.number_literal(ctx, *loc, int, expr, false)
            }
            HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
            HexStringLiteral(lit, _) => self.hex_literals(ctx, &[lit.clone()]),
            StringLiteral(lit, _) => self.string_literal(ctx, lit.loc, &lit.string),
            Variable(ident) => self.variable(ident, ctx, None),
            FunctionCall(yul_func_call) => self.yul_func_call(yul_func_call, ctx),
            SuffixAccess(_loc, _yul_member_expr, _ident) => Err(ExprErr::Todo(
                expr.loc(),
                "Yul member access not yet supported".to_string(),
            )),
        }
    }

    fn match_assign_yul(
        &mut self,
        loc: Loc,
        nodes: &[ContextVarNode],
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret {
            s @ ExprRet::Single(_) | s @ ExprRet::SingleLiteral(_) => {
                self.match_assign_yul_inner(loc, &nodes[0], s)?;
            }
            ExprRet::Multi(inner) => {
                if inner.len() == nodes.len() {
                    inner
                        .into_iter()
                        .zip(nodes.iter())
                        .map(|(ret, node)| self.match_assign_yul_inner(loc, node, ret))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                } else {
                    return Err(ExprErr::Todo(
                        loc,
                        "Differing number of assignees and assignors in yul expression".to_string(),
                    ));
                };
            }
            ExprRet::Fork(w1, w2) => {
                self.match_assign_yul(loc, nodes, *w1)?;
                self.match_assign_yul(loc, nodes, *w2)?;
            }
            ExprRet::CtxKilled => {}
        }

        Ok(())
    }

    fn match_assign_yul_inner(
        &mut self,
        loc: Loc,
        node: &ContextVarNode,
        ret: ExprRet,
    ) -> Result<(), ExprErr> {
        match ret.flatten() {
            ExprRet::Single((_ctx, idx)) | ExprRet::SingleLiteral((_ctx, idx)) => {
                let assign = ContextVarNode::from(idx);
                let assign_ty = assign.underlying(self).into_expr_err(loc)?.ty.clone();
                if assign_ty.is_dyn(self).into_expr_err(loc)? {
                    let b_ty = self.builtin_or_add(Builtin::Bytes(32));
                    node.underlying_mut(self).into_expr_err(loc)?.ty =
                        VarType::try_from_idx(self, b_ty).unwrap();
                } else {
                    node.underlying_mut(self).into_expr_err(loc)?.ty = assign_ty;
                }
            }
            ExprRet::Multi(_inner) => {
                return Err(ExprErr::Todo(
                    loc,
                    "Multi in single assignment yul expression is unhandled".to_string(),
                ))
            }
            ExprRet::Fork(w1, w2) => {
                self.match_assign_yul_inner(loc, node, *w1)?;
                self.match_assign_yul_inner(loc, node, *w2)?;
            }
            ExprRet::CtxKilled => {}
        }
        Ok(())
    }
}
