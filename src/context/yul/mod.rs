use crate::context::exprs::IntoExprErr;
use crate::context::ContextBuilder;
use crate::context::ExprParser;
use crate::AnalyzerLike;
use crate::ExprErr;
use shared::context::ContextVar;
use shared::context::ContextVarNode;
use shared::context::ExprRet;
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
        println!("ctx: {}, yul stmt: {:?}", ctx.path(self), stmt);

        let res = ctx.pop_expr(stmt.loc(), self).into_expr_err(stmt.loc());
        let _ = self.add_if_err(res);
        println!("popped");

        if ctx.is_killed(self).unwrap() {
            return;
        }
        let ret = self.apply_to_edges(ctx, stmt.loc(), &|analyzer, ctx, _loc| {
            match stmt {
                Assign(loc, yul_exprs, yul_expr) => {
                    match yul_exprs
                        .iter()
                        .try_for_each(|expr| analyzer.parse_ctx_yul_expr(expr, ctx))
                    {
                        Ok(()) => {
                            analyzer.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(lhs_side) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoLhs(loc, "No left hand side assignments in yul block".to_string()))
                                };
                                if matches!(lhs_side, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(lhs_side, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }

                                analyzer.parse_ctx_yul_expr(yul_expr, ctx)?;
                                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                    let Some(rhs_side) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                                        return Err(ExprErr::NoRhs(loc, "No right hand side assignments in yul block".to_string()))
                                    };

                                    if matches!(rhs_side, ExprRet::CtxKilled(_)) {
                                        ctx.push_expr(rhs_side, analyzer).into_expr_err(loc)?;
                                        return Ok(());
                                    }

                                    analyzer.match_assign_sides(
                                        ctx,
                                        loc,
                                        &lhs_side,
                                        &rhs_side,
                                    )
                                })
                            })
                        }
                        Err(e) => Err(e),
                    }
                }
                VariableDeclaration(loc, yul_idents, maybe_yul_expr) => {
                    let nodes = yul_idents
                        .iter()
                        .map(|ident| {
                            let b_ty = analyzer.builtin_or_add(Builtin::Uint(256));
                            let var = ContextVar {
                                loc: Some(ident.loc),
                                name: ident.id.name.clone(),
                                display_name: ident.id.name.clone(),
                                storage: None,
                                is_tmp: false,
                                tmp_of: None,
                                is_symbolic: true,
                                is_return: false,
                                ty: VarType::try_from_idx(analyzer, b_ty).unwrap(),
                            };
                            let cvar = ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
                            analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                            analyzer.advance_var_in_ctx(cvar, *loc, ctx).unwrap()
                        })
                        .collect::<Vec<_>>();

                    if let Some(yul_expr) = maybe_yul_expr {
                        analyzer.parse_ctx_yul_expr(yul_expr, ctx)?;
                        analyzer.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                            let Some(ret) = ctx.pop_expr(loc, analyzer).into_expr_err(loc)? else {
                                return Err(ExprErr::NoRhs(loc, "No right hand side assignments in yul block".to_string()))
                            };

                            if matches!(ret, ExprRet::CtxKilled(_)) {
                                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                                return Ok(());
                            }

                            analyzer.match_assign_yul(ctx, loc, &nodes, ret)

                        })
                    } else {
                        Ok(())
                    }
                }
                If(loc, yul_expr, yul_block) => {
                    analyzer.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                        let ret = analyzer.yul_cond_op_stmt(loc, yul_expr, yul_block, ctx);
                        let _ = analyzer.add_if_err(ret);
                        Ok(())
                    })
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
                    loc,
                    condition,
                    cases,
                    default,
                }) => {
                    // todo!()
                    analyzer.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                        analyzer.yul_switch_stmt(loc, condition.clone(), cases.to_vec(), default.clone(), ctx)
                    })
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
                        .for_each(|stmt| analyzer.parse_ctx_yul_stmt_inner(stmt, ctx));
                    Ok(())
                }
                FunctionDefinition(_yul_func_def) => {
                    todo!()
                }
                FunctionCall(yul_func_call) => {
                    analyzer.yul_func_call(yul_func_call, ctx)
                }
                Error(_loc) => {
                    todo!()
                }
            }
        });
        let _ = self.add_if_err(ret);
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn parse_ctx_yul_expr(
        &mut self,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        tracing::trace!("Parsing yul expression: {expr:?}");

        let edges = ctx.live_edges(self).into_expr_err(expr.loc())?;
        if edges.is_empty() {
            self.parse_ctx_yul_expr_inner(expr, ctx)
        } else {
            edges
                .iter()
                .try_for_each(|fork_ctx| self.parse_ctx_yul_expr(expr, *fork_ctx))?;
            Ok(())
        }
    }

    fn parse_ctx_yul_expr_inner(
        &mut self,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
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
        _ctx: ContextNode,
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
                        format!("Differing number of assignees and assignors in yul expression, assignors: {}, assignees: {}", nodes.len(), inner.len()),
                    ));
                };
            }
            ExprRet::CtxKilled(_kind) => {}
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
            ExprRet::Single(idx) | ExprRet::SingleLiteral(idx) => {
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
            ExprRet::CtxKilled(..) => {}
        }
        Ok(())
    }
}
