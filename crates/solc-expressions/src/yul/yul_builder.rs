//! Trait and blanket implementation for parsing yul-based statements and expressions

use crate::ExpressionParser;

use graph::{
    elem::Elem,
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, SolcRange, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use solang_parser::pt::{Expression, Loc, YulExpression, YulStatement};

impl<T> YulBuilder for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser
{
}
/// Trait that processes Yul statements and expressions
pub trait YulBuilder:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser
{
    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self)))]
    /// Parse a yul statement
    fn parse_ctx_yul_statement(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &YulStatement,
        ctx: ContextNode,
    ) where
        Self: Sized,
    {
        panic!("here");
        // if let Some(true) = self.add_if_err(ctx.is_ended(self).into_expr_err(stmt.loc())) {
        //     return;
        // }
        // if let Some(live_edges) = self.add_if_err(ctx.live_edges(self).into_expr_err(stmt.loc())) {
        //     if live_edges.is_empty() {
        //         self.parse_ctx_yul_stmt_inner(arena, stmt, ctx)
        //     } else {
        //         live_edges.iter().for_each(|fork_ctx| {
        //             self.parse_ctx_yul_stmt_inner(arena, stmt, *fork_ctx);
        //         });
        //     }
        // }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// After doing some setup in `parse_ctx_yul_statement`, actually parse a yul statement
    fn parse_ctx_yul_stmt_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &YulStatement,
        ctx: ContextNode,
    ) where
        Self: Sized,
    {
        panic!("here");
        // use YulStatement::*;
        // println!("ctx: {}, yul stmt: {:?}", ctx.path(self), stmt);

        // let res = ctx
        //     .pop_expr_latest(stmt.loc(), self)
        //     .into_expr_err(stmt.loc());
        // let _ = self.add_if_err(res);

        // if ctx.is_killed(self).unwrap() {
        //     return;
        // }
        // let ret = self.apply_to_edges(ctx, stmt.loc(), arena, &|analyzer, arena, ctx, _loc| {
        //     match stmt {
        //         Assign(loc, yul_exprs, yul_expr) => {
        //             match yul_exprs
        //                 .iter()
        //                 .try_for_each(|expr| analyzer.parse_ctx_yul_expr(arena, expr, ctx))
        //             {
        //                 Ok(()) => analyzer.apply_to_edges(
        //                     ctx,
        //                     *loc,
        //                     arena,
        //                     &|analyzer, arena, ctx, loc| {
        //                         let Some(lhs_side) =
        //                             ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //                         else {
        //                             return Err(ExprErr::NoLhs(
        //                                 loc,
        //                                 "No left hand side assignments in yul block".to_string(),
        //                             ));
        //                         };
        //                         if matches!(lhs_side, ExprRet::CtxKilled(_)) {
        //                             ctx.push_expr(lhs_side, analyzer).into_expr_err(loc)?;
        //                             return Ok(());
        //                         }

        //                         analyzer.parse_ctx_yul_expr(arena, yul_expr, ctx)?;
        //                         analyzer.apply_to_edges(
        //                             ctx,
        //                             loc,
        //                             arena,
        //                             &|analyzer, arena, ctx, loc| {
        //                                 let Some(rhs_side) = ctx
        //                                     .pop_expr_latest(loc, analyzer)
        //                                     .into_expr_err(loc)?
        //                                 else {
        //                                     return Err(ExprErr::NoRhs(
        //                                         loc,
        //                                         "No right hand side assignments in yul block"
        //                                             .to_string(),
        //                                     ));
        //                                 };

        //                                 if matches!(rhs_side, ExprRet::CtxKilled(_)) {
        //                                     ctx.push_expr(rhs_side, analyzer).into_expr_err(loc)?;
        //                                     return Ok(());
        //                                 }

        //                                 analyzer.match_assign_sides(
        //                                     arena, ctx, loc, &lhs_side, &rhs_side,
        //                                 )
        //                             },
        //                         )
        //                     },
        //                 ),
        //                 Err(e) => Err(e),
        //             }
        //         }
        //         VariableDeclaration(loc, yul_idents, maybe_yul_expr) => {
        //             let nodes = yul_idents
        //                 .iter()
        //                 .map(|ident| {
        //                     let b_ty = analyzer.builtin_or_add(Builtin::Uint(256));
        //                     let var = ContextVar {
        //                         loc: Some(ident.loc),
        //                         name: ident.id.name.clone(),
        //                         display_name: ident.id.name.clone(),
        //                         storage: None,
        //                         is_tmp: false,
        //                         tmp_of: None,
        //                         dep_on: None,
        //                         is_symbolic: true,
        //                         is_return: false,
        //                         ty: VarType::try_from_idx(analyzer, b_ty).unwrap(),
        //                     };
        //                     let cvar =
        //                         ContextVarNode::from(analyzer.add_node(Node::ContextVar(var)));
        //                     ctx.add_var(cvar, analyzer).unwrap();
        //                     analyzer.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
        //                     analyzer.advance_var_in_ctx(cvar, *loc, ctx).unwrap()
        //                 })
        //                 .collect::<Vec<_>>();

        //             if let Some(yul_expr) = maybe_yul_expr {
        //                 analyzer.parse_ctx_yul_expr(arena, yul_expr, ctx)?;
        //                 analyzer.apply_to_edges(ctx, *loc, arena, &|analyzer, _arena, ctx, loc| {
        //                     let Some(ret) =
        //                         ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
        //                     else {
        //                         return Err(ExprErr::NoRhs(
        //                             loc,
        //                             "No right hand side assignments in yul block".to_string(),
        //                         ));
        //                     };

        //                     if matches!(ret, ExprRet::CtxKilled(_)) {
        //                         ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
        //                         return Ok(());
        //                     }

        //                     analyzer.match_assign_yul(ctx, loc, &nodes, ret)
        //                 })
        //             } else {
        //                 Ok(())
        //             }
        //         }
        //         If(loc, yul_expr, yul_block) => {
        //             analyzer.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
        //                 let ret = analyzer.yul_cond_op_stmt(arena, loc, yul_expr, yul_block, ctx);
        //                 let _ = analyzer.add_if_err(ret);
        //                 Ok(())
        //             })
        //         }
        //         For(YulFor {
        //             loc,
        //             init_block: _,
        //             condition: _,
        //             post_block: _,
        //             execution_block: _,
        //         }) => {
        //             let sctx =
        //                 Context::add_subctx(ctx, None, *loc, None, None, false, analyzer, None)
        //                     .into_expr_err(*loc)?;
        //             let subctx = ContextNode::from(analyzer.add_node(Node::Context(sctx)));
        //             ctx.set_child_call(subctx, analyzer).into_expr_err(*loc)?;
        //             analyzer.apply_to_edges(subctx, *loc, arena, &|analyzer, arena, subctx, loc| {
        //                 let vars = subctx.local_vars(analyzer).clone();
        //                 vars.iter().for_each(|(name, var)| {
        //                     // widen to max range
        //                     if let Some(inheritor_var) = ctx.var_by_name(analyzer, name) {
        //                         let inheritor_var = inheritor_var.latest_version(analyzer);
        //                         if let Some(r) = var
        //                             .underlying(analyzer)
        //                             .unwrap()
        //                             .ty
        //                             .default_range(analyzer)
        //                             .unwrap()
        //                         {
        //                             let new_inheritor_var = analyzer
        //                                 .advance_var_in_ctx(inheritor_var, loc, ctx)
        //                                 .unwrap();
        //                             let res = new_inheritor_var
        //                                 .set_range_min(analyzer, arena, r.min)
        //                                 .into_expr_err(loc);
        //                             let _ = analyzer.add_if_err(res);
        //                             let res = new_inheritor_var
        //                                 .set_range_max(analyzer, arena, r.max)
        //                                 .into_expr_err(loc);
        //                             let _ = analyzer.add_if_err(res);
        //                         }
        //                     }
        //                 });
        //                 Ok(())
        //             })
        //         }
        //         Switch(YulSwitch {
        //             loc,
        //             condition,
        //             cases,
        //             default,
        //         }) => analyzer.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
        //             analyzer.yul_switch_stmt(
        //                 arena,
        //                 loc,
        //                 condition.clone(),
        //                 cases.to_vec(),
        //                 default.clone(),
        //                 ctx,
        //             )
        //         }),
        //         Leave(loc) => Err(ExprErr::Todo(
        //             *loc,
        //             "Yul `leave` statements are not currently supported".to_string(),
        //         )),
        //         Break(loc) => Err(ExprErr::Todo(
        //             *loc,
        //             "Yul `break` statements are not currently supported".to_string(),
        //         )),
        //         Continue(loc) => Err(ExprErr::Todo(
        //             *loc,
        //             "Yul `continue` statements are not currently supported".to_string(),
        //         )),
        //         Block(yul_block) => {
        //             yul_block
        //                 .statements
        //                 .iter()
        //                 .for_each(|stmt| analyzer.parse_ctx_yul_stmt_inner(arena, stmt, ctx));
        //             Ok(())
        //         }
        //         FunctionDefinition(yul_func_def) => Err(ExprErr::Todo(
        //             yul_func_def.loc(),
        //             "Yul `function` defintions are not currently supported".to_string(),
        //         )),
        //         FunctionCall(yul_func_call) => analyzer.yul_func_call(arena, yul_func_call, ctx),
        //         Error(loc) => Err(ExprErr::ParseError(
        //             *loc,
        //             "Could not parse this yul statement".to_string(),
        //         )),
        //     }
        // });
        // let _ = self.add_if_err(ret);
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Parse a yul expression
    fn parse_ctx_yul_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        panic!("here");
        // tracing::trace!("Parsing yul expression: {expr:?}");

        // let edges = ctx.live_edges(self).into_expr_err(expr.loc())?;
        // if edges.is_empty() {
        //     self.parse_ctx_yul_expr_inner(arena, expr, ctx)
        // } else {
        //     edges
        //         .iter()
        //         .try_for_each(|fork_ctx| self.parse_ctx_yul_expr(arena, expr, *fork_ctx))?;
        //     Ok(())
        // }
    }

    /// After performing some setup in `parse_ctx_yul_expr`, actually parse the yul expression
    fn parse_ctx_yul_expr_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        expr: &YulExpression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        panic!("here");
        // use YulExpression::*;
        // match expr {
        //     BoolLiteral(loc, b, _) => self.bool_literal(ctx, *loc, *b),
        //     NumberLiteral(loc, int, expr, unit) => {
        //         self.number_literal(ctx, *loc, int, expr, false, unit)
        //     }
        //     HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
        //     HexStringLiteral(lit, _) => self.hex_literals(ctx, &[lit.clone()]),
        //     StringLiteral(lit, _) => self.string_literal(ctx, lit.loc, &lit.string),
        //     Variable(ident) => {
        //         self.variable(arena, ident, ctx, None, None)?;
        //         self.apply_to_edges(ctx, ident.loc, arena, &|analyzer, _arena, edge_ctx, loc| {
        //             if let Some(ret) = edge_ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? {
        //                 if ContextVarNode::from(ret.expect_single().into_expr_err(loc)?)
        //                     .is_memory(analyzer)
        //                     .into_expr_err(loc)?
        //                 {
        //                     // its a memory based variable, push a uint instead
        //                     let b = Builtin::Uint(256);
        //                     let var = ContextVar::new_from_builtin(
        //                         loc,
        //                         analyzer.builtin_or_add(b).into(),
        //                         analyzer,
        //                     )
        //                     .into_expr_err(loc)?;
        //                     let node = analyzer.add_node(Node::ContextVar(var));
        //                     edge_ctx
        //                         .push_expr(ExprRet::Single(node), analyzer)
        //                         .into_expr_err(loc)
        //                 } else {
        //                     edge_ctx.push_expr(ret, analyzer).into_expr_err(loc)
        //                 }
        //             } else {
        //                 Err(ExprErr::Unresolved(
        //                     ident.loc,
        //                     format!("Could not find variable with name: {}", ident.name),
        //                 ))
        //             }
        //         })
        //     }
        //     FunctionCall(yul_func_call) => self.yul_func_call(arena, yul_func_call, ctx),
        //     SuffixAccess(loc, yul_member_expr, ident) => {
        //         self.parse_inputs(arena, ctx, *loc, &[*yul_member_expr.clone()])?;

        //         self.apply_to_edges(ctx, *loc, arena, &|analyzer, _arena, ctx, loc| {
        //             let Ok(Some(lhs)) = ctx.pop_expr_latest(loc, analyzer) else {
        //                 return Err(ExprErr::NoLhs(
        //                     loc,
        //                     "`.slot` had no left hand side".to_string(),
        //                 ));
        //             };
        //             match &*ident.name {
        //                 "slot" => {
        //                     let slot_var = analyzer.slot(
        //                         ctx,
        //                         loc,
        //                         lhs.expect_single().into_expr_err(loc)?.into(),
        //                     );
        //                     ctx.push_expr(ExprRet::Single(slot_var.into()), analyzer)
        //                         .into_expr_err(loc)?;
        //                     Ok(())
        //                 }
        //                 _ => Err(ExprErr::Todo(
        //                     expr.loc(),
        //                     format!("Yul member access `{}` not yet supported", ident.name),
        //                 )),
        //             }
        //         })
        //     }
        // }
    }

    /// Match [`ExprRet`] from the sides of an `YulAssign` to perform the assignment
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
            ExprRet::Null => {}
        }

        Ok(())
    }

    /// Perform the actual yul assignment
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
            ExprRet::Null => {}
        }
        Ok(())
    }

    fn slot(&mut self, ctx: ContextNode, loc: Loc, lhs: ContextVarNode) -> ContextVarNode {
        let lhs = lhs.first_version(self);
        let name = format!("{}.slot", lhs.name(self).unwrap());
        tracing::trace!("Slot access: {}", name);
        if let Some(attr_var) = ctx.var_by_name_or_recurse(self, &name).unwrap() {
            attr_var.latest_version_or_inherited_in_ctx(ctx, self)
        } else {
            let slot_var = ContextVar {
                loc: Some(loc),
                name: lhs.name(self).unwrap() + ".slot",
                display_name: lhs.display_name(self).unwrap() + ".slot",
                storage: None,
                is_tmp: false,
                tmp_of: None,
                dep_on: None,
                is_symbolic: true,
                is_return: false,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    SolcRange::try_from_builtin(&Builtin::Uint(256)),
                ),
            };
            let slot_node = self.add_node(slot_var);

            self.add_edge(slot_node, lhs, Edge::Context(ContextEdge::SlotAccess));
            self.add_edge(slot_node, ctx, Edge::Context(ContextEdge::Variable));
            ctx.add_var(slot_node.into(), self).unwrap();
            slot_node.into()
        }
    }
}
