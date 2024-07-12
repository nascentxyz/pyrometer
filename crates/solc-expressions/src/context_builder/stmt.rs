use crate::{
    context_builder::ContextBuilder,
    func_call::{func_caller::FuncCaller, modifier::ModifierCaller},
    loops::Looper,
    yul::YulBuilder,
    ExpressionParser, TestCommandRunner,
};

use graph::{
    elem::Elem,
    nodes::{
        Concrete, Context, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode,
        FunctionParamNode, FunctionReturnNode, KilledKind,
    },
    AnalyzerBackend, ContextEdge, Edge, Node,
};
use shared::{ExprErr, IntoExprErr, NodeIdx, RangeArena};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Statement, YulStatement},
};

impl<T> StatementParser for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser
{
}

/// Solidity statement parser
pub trait StatementParser:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExpressionParser + TestCommandRunner
{
    /// Performs setup for parsing a solidity statement
    fn parse_ctx_statement(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Copy>,
    ) where
        Self: Sized,
    {
        if let Some(parent) = parent_ctx {
            match self.node(parent) {
                Node::Context(_) => {
                    let ctx = ContextNode::from(parent.into());
                    if !ctx.killed_or_ret(self).unwrap() {
                        if let Some(live_edges) =
                            self.add_if_err(ctx.live_edges(self).into_expr_err(stmt.loc()))
                        {
                            if live_edges.is_empty() {
                                self.parse_ctx_stmt_inner(arena, stmt, unchecked, parent_ctx)
                            } else {
                                live_edges.iter().for_each(|fork_ctx| {
                                    self.parse_ctx_stmt_inner(
                                        arena,
                                        stmt,
                                        unchecked,
                                        Some(*fork_ctx),
                                    );
                                });
                            }
                        }
                    }
                }
                _ => self.parse_ctx_stmt_inner(arena, stmt, unchecked, parent_ctx),
            }
        } else {
            self.parse_ctx_stmt_inner(arena, stmt, unchecked, parent_ctx)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Performs parsing of a solidity statement
    fn parse_ctx_stmt_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Copy>,
    ) where
        Self: Sized,
    {
        use Statement::*;
        // tracing::trace!(
        //     "stmt: {:#?}, node: {:#?}",
        //     stmt,
        //     if let Some(node) = parent_ctx {
        //         Some(self.node(node.into()))
        //     } else {
        //         None
        //     }
        // );

        // at the end of a statement we shouldn't have anything in the stack?
        if let Some(ctx) = parent_ctx {
            if let Node::Context(_) = self.node(ctx) {
                let c = ContextNode::from(ctx.into());
                let res = self.is_representation_ok(arena).into_expr_err(stmt.loc());
                if let Some(errs) = self.add_if_err(res) {
                    if !errs.is_empty() {
                        let Some(is_killed) =
                            self.add_if_err(c.is_killed(self).into_expr_err(stmt.loc()))
                        else {
                            return;
                        };
                        if !is_killed {
                            c.kill(self, stmt.loc(), KilledKind::ParseError).unwrap();
                            errs.into_iter().for_each(|err| {
                                self.add_expr_err(ExprErr::from_repr_err(stmt.loc(), err));
                            });
                        }
                    }
                }

                let _ = c.pop_expr_latest(stmt.loc(), self);
                if unchecked {
                    let _ = c.set_unchecked(self);
                } else {
                    let _ = c.unset_unchecked(self);
                }

                if c.killed_or_ret(self).unwrap() {
                    return;
                }
            }
        }

        match stmt {
            Block {
                loc,
                unchecked,
                statements,
            } => {
                tracing::trace!("parsing block");
                let parent = parent_ctx.expect("Free floating contexts shouldn't happen");
                let mut entry_loc = None;
                let mut mods_set = false;
                let ctx_node = match self.node(parent) {
                    Node::Function(fn_node) => {
                        mods_set = fn_node.modifiers_set;
                        entry_loc = Some(fn_node.loc);
                        tracing::trace!("creating genesis context for function");
                        let ctx = Context::new(
                            FunctionNode::from(parent.into()),
                            self.add_if_err(
                                FunctionNode::from(parent.into())
                                    .name(self)
                                    .into_expr_err(stmt.loc()),
                            )
                            .unwrap(),
                            *loc,
                        );
                        let ctx_node = self.add_node(Node::Context(ctx));
                        self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Context));

                        ctx_node
                    }
                    Node::Context(_) => {
                        // let ctx = Context::new_subctx(
                        //     ContextNode::from(parent.into()),
                        //     *loc,
                        //     false,
                        //     self,
                        // );
                        // let ctx_node = self.add_node(Node::Context(ctx));
                        // self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Subcontext));
                        // ctx_node
                        parent.into()
                    }
                    e => todo!(
                        "Expected a context to be created by a function or context but got: {:?}",
                        e
                    ),
                };

                // optionally add named input and named outputs into context
                let (params, inputs): (Vec<_>, Vec<_>) = self
                    .graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionParam)
                    .map(|edge| FunctionParamNode::from(edge.source()))
                    .collect::<Vec<FunctionParamNode>>()
                    .into_iter()
                    .filter_map(|param_node| {
                        let res = param_node
                            .underlying(self)
                            .into_expr_err(stmt.loc())
                            .cloned();
                        let func_param = self.add_if_err(res)?;
                        if let Some(cvar) = ContextVar::maybe_new_from_func_param(self, func_param)
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            ContextNode::from(ctx_node)
                                .add_var(cvar_node.into(), self)
                                .unwrap();
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );

                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::CalldataVariable),
                            );

                            let ty = ContextVarNode::from(cvar_node).ty(self).unwrap();
                            if let Some(strukt) = ty.maybe_struct() {
                                strukt
                                    .add_fields_to_cvar(self, *loc, ContextVarNode::from(cvar_node))
                                    .unwrap();
                            }

                            Some((param_node, ContextVarNode::from(cvar_node)))
                        } else {
                            None
                        }
                    })
                    .unzip();

                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionReturn)
                    .map(|edge| FunctionReturnNode::from(edge.source()))
                    .collect::<Vec<FunctionReturnNode>>()
                    .iter()
                    .for_each(|ret_node| {
                        let res = ret_node.underlying(self).into_expr_err(stmt.loc()).cloned();
                        let func_ret = self.add_if_err(res).unwrap();
                        if let Some(cvar) = ContextVar::maybe_new_from_func_ret(self, func_ret) {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            ContextNode::from(ctx_node)
                                .add_var(cvar_node.into(), self)
                                .unwrap();
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                if let Some(fn_loc) = entry_loc {
                    if !mods_set {
                        let parent = FunctionNode::from(parent.into());
                        let _ = self
                            .set_modifiers(arena, parent, ctx_node.into())
                            .map_err(|e| self.add_expr_err(e));
                    }

                    let res = self.func_call_inner(
                        arena,
                        true,
                        ctx_node.into(),
                        parent.into().into(),
                        fn_loc,
                        &inputs,
                        &params,
                        None,
                        &None,
                    );
                    if self.widen_if_limit_hit(ctx_node.into(), res) {
                        return;
                    }
                    let res = self.apply_to_edges(
                        ctx_node.into(),
                        *loc,
                        arena,
                        &|analyzer, _arena, ctx, loc| {
                            if ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                                tracing::trace!("killing due to bad funciton call");
                                let res = ContextNode::from(ctx_node)
                                    .kill(
                                        analyzer,
                                        fn_loc,
                                        ctx.underlying(analyzer).unwrap().killed.unwrap().1,
                                    )
                                    .into_expr_err(fn_loc);
                                let _ = analyzer.add_if_err(res);
                            }
                            Ok(())
                        },
                    );

                    if self.widen_if_limit_hit(ctx_node.into(), res) {
                        return;
                    }

                    return;
                }

                let res = self.apply_to_edges(
                    ctx_node.into(),
                    *loc,
                    arena,
                    &|analyzer, arena, ctx, _loc| {
                        statements.iter().for_each(|stmt| {
                            analyzer.parse_ctx_statement(arena, stmt, *unchecked, Some(ctx))
                        });
                        Ok(())
                    },
                );
                if self.widen_if_limit_hit(ctx_node.into(), res) {}
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                tracing::trace!(
                    "parsing variable definition, {:?} {var_decl:?}",
                    ctx.path(self)
                );

                if let Some(rhs) = maybe_expr {
                    match self.parse_ctx_expr(arena, rhs, ctx) {
                        Ok(()) => {
                            let res = self.apply_to_edges(
                                ctx,
                                *loc,
                                arena,
                                &|analyzer, arena, ctx, loc| {
                                    if !ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                                        let Some(rhs_paths) = ctx
                                            .pop_expr_latest(loc, analyzer)
                                            .into_expr_err(loc)?
                                        else {
                                            return Err(ExprErr::NoRhs(
                                                loc,
                                                format!(
                                                "Variable definition had no right hand side, {}",
                                                ctx.path(analyzer)
                                            ),
                                            ));
                                        };

                                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                                            ctx.push_expr(rhs_paths, analyzer)
                                                .into_expr_err(loc)?;
                                            return Ok(());
                                        }

                                        if let solang_parser::pt::Expression::Variable(ident) =
                                            &var_decl.ty
                                        {
                                            analyzer.apply_to_edges(
                                                ctx,
                                                ident.loc,
                                                arena,
                                                &|analyzer, arena, ctx, _| {
                                                    analyzer.variable(
                                                        arena,
                                                        ident,
                                                        ctx,
                                                        var_decl.storage.clone(),
                                                        None,
                                                    )
                                                },
                                            )?;
                                        } else {
                                            analyzer.parse_ctx_expr(arena, &var_decl.ty, ctx)?;
                                        }

                                        analyzer.apply_to_edges(
                                            ctx,
                                            loc,
                                            arena,
                                            &|analyzer, arena, ctx, loc| {
                                                let Some(lhs_paths) = ctx
                                                    .pop_expr_latest(loc, analyzer)
                                                    .into_expr_err(loc)?
                                                else {
                                                    return Err(ExprErr::NoLhs(
                                                        loc,
                                                        "Variable definition had no left hand side"
                                                            .to_string(),
                                                    ));
                                                };

                                                if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                                                    ctx.push_expr(lhs_paths, analyzer)
                                                        .into_expr_err(loc)?;
                                                    return Ok(());
                                                }
                                                analyzer.match_var_def(
                                                    arena,
                                                    ctx,
                                                    var_decl,
                                                    loc,
                                                    &lhs_paths,
                                                    Some(&rhs_paths),
                                                )?;
                                                Ok(())
                                            },
                                        )
                                    } else {
                                        Ok(())
                                    }
                                },
                            );
                            let _ = self.widen_if_limit_hit(ctx, res);
                        }
                        ret => {
                            let _ = self.widen_if_limit_hit(ctx, ret);
                        }
                    }
                } else {
                    let res = if let solang_parser::pt::Expression::Variable(ident) = &var_decl.ty {
                        self.apply_to_edges(ctx, ident.loc, arena, &|analyzer, arena, ctx, _| {
                            analyzer.variable(arena, ident, ctx, var_decl.storage.clone(), None)
                        })
                    } else {
                        self.parse_ctx_expr(arena, &var_decl.ty, ctx)
                    };

                    if self.widen_if_limit_hit(ctx, res) {
                        return;
                    }
                    let res =
                        self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                            let Some(lhs_paths) =
                                ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                            else {
                                return Err(ExprErr::NoLhs(
                                    loc,
                                    "Variable definition had no left hand side".to_string(),
                                ));
                            };

                            if matches!(lhs_paths, ExprRet::CtxKilled(_)) {
                                ctx.push_expr(lhs_paths, analyzer).into_expr_err(loc)?;
                                return Ok(());
                            }
                            analyzer.match_var_def(arena, ctx, var_decl, loc, &lhs_paths, None)?;
                            Ok(())
                        });
                    let _ = self.widen_if_limit_hit(ctx, res);
                }
            }
            Args(_loc, _args) => {
                tracing::trace!("parsing args, {_args:?}");
            }
            If(loc, if_expr, true_expr, maybe_false_expr) => {
                tracing::trace!("parsing if, {if_expr:?}");
                let ctx = ContextNode::from(parent_ctx.expect("Dangling if statement").into());
                let res = self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, loc| {
                    analyzer.cond_op_stmt(arena, loc, if_expr, true_expr, maybe_false_expr, ctx)
                });
                let _ = self.widen_if_limit_hit(ctx, res);
            }
            While(loc, cond, body) => {
                tracing::trace!("parsing while, {cond:?}");
                if let Some(parent) = parent_ctx {
                    let res = self.apply_to_edges(
                        ContextNode::from(parent.into()),
                        *loc,
                        arena,
                        &|analyzer, arena, ctx, loc| {
                            analyzer.while_loop(arena, loc, ctx, cond, body)
                        },
                    );
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
            }
            Expression(loc, expr) => {
                tracing::trace!("parsing expr, {expr:?}");
                if let Some(parent) = parent_ctx {
                    let ctx = parent.into().into();
                    if let solang_parser::pt::Expression::StringLiteral(lits) = expr {
                        if lits.len() == 1 {
                            if let Some(command) = self.test_string_literal(&lits[0].string) {
                                let _ = self.apply_to_edges(
                                    ctx,
                                    *loc,
                                    arena,
                                    &|analyzer, arena, ctx, loc| {
                                        analyzer.run_test_command(arena, ctx, loc, command.clone());
                                        Ok(())
                                    },
                                );
                            }
                        }
                    }

                    match self.parse_ctx_expr(arena, expr, ctx) {
                        Ok(()) => {
                            let res = self.apply_to_edges(
                                ctx,
                                *loc,
                                arena,
                                &|analyzer, _arena, ctx, loc| {
                                    if ctx.killed_or_ret(analyzer).into_expr_err(loc)? {
                                        tracing::trace!("killing due to bad expr");
                                        ContextNode::from(parent.into())
                                            .kill(
                                                analyzer,
                                                loc,
                                                ctx.underlying(analyzer).unwrap().killed.unwrap().1,
                                            )
                                            .into_expr_err(loc)?;
                                    }
                                    Ok(())
                                },
                            );
                            let _ = self.widen_if_limit_hit(ctx, res);
                        }
                        e => {
                            let _ = self.widen_if_limit_hit(ctx, e);
                        }
                    }
                }
            }
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {
                tracing::trace!("parsing for loop");
                if let Some(parent) = parent_ctx {
                    let res = self.apply_to_edges(
                        parent.into().into(),
                        *loc,
                        arena,
                        &|analyzer, arena, ctx, loc| {
                            analyzer.for_loop(
                                arena,
                                loc,
                                ctx,
                                maybe_for_start,
                                maybe_for_middle,
                                maybe_for_end,
                                maybe_for_body,
                            )
                        },
                    );
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
            }
            DoWhile(loc, while_stmt, while_expr) => {
                tracing::trace!("parsing `do while`, {while_expr:?}");
                if let Some(parent) = parent_ctx {
                    let res = self.apply_to_edges(
                        ContextNode::from(parent.into()),
                        *loc,
                        arena,
                        &|analyzer, arena, ctx, loc| {
                            analyzer.while_loop(arena, loc, ctx, while_expr, while_stmt)
                        },
                    );
                    let _ = self.widen_if_limit_hit(parent.into().into(), res);
                }
            }
            Continue(_loc) => {
                tracing::trace!("parsing continue");
                // TODO: We cheat in loops by just widening so continues dont matter yet
            }
            Break(_loc) => {
                tracing::trace!("parsing break");
                // TODO: We cheat in loops by just widening so breaks dont matter yet
            }
            Assembly {
                loc,
                dialect: _,
                flags: _,
                block: yul_block,
            } => {
                tracing::trace!("parsing assembly");
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                let res = self.apply_to_edges(ctx, *loc, arena, &|analyzer, arena, ctx, _loc| {
                    analyzer.parse_ctx_yul_statement(
                        arena,
                        &YulStatement::Block(yul_block.clone()),
                        ctx,
                    );
                    Ok(())
                });
                let _ = self.widen_if_limit_hit(ctx, res);
            }
            Return(loc, maybe_ret_expr) => {
                tracing::trace!("parsing return");
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let res = self.parse_ctx_expr(arena, ret_expr, parent.into().into());
                        if self.widen_if_limit_hit(parent.into().into(), res) {
                            return;
                        }
                        let res = self.apply_to_edges(
                            parent.into().into(),
                            *loc,
                            arena,
                            &|analyzer, arena, ctx, loc| {
                                let Ok(Some(ret)) = ctx.pop_expr_latest(loc, analyzer) else {
                                    return Err(ExprErr::NoLhs(
                                        loc,
                                        "Return did not have a associated expression".to_string(),
                                    ));
                                };

                                if matches!(ret, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }

                                let paths = ret.flatten();
                                if paths.is_killed() {
                                    tracing::trace!("killing due to bad return");
                                    let res = ContextNode::from(parent.into())
                                        .kill(analyzer, loc, paths.killed_kind().unwrap())
                                        .into_expr_err(loc);
                                    let _ = analyzer.add_if_err(res);
                                    return Ok(());
                                }
                                analyzer.return_match(arena, ctx, &loc, &paths, 0);
                                Ok(())
                            },
                        );
                        let _ = self.widen_if_limit_hit(parent.into().into(), res);
                    }
                }
            }
            Revert(loc, _maybe_err_path, _exprs) => {
                tracing::trace!("parsing revert");
                if let Some(parent) = parent_ctx {
                    let parent = ContextNode::from(parent.into());
                    let res =
                        self.apply_to_edges(parent, *loc, arena, &|analyzer, _arena, ctx, loc| {
                            let res = ctx
                                .kill(analyzer, loc, KilledKind::Revert)
                                .into_expr_err(loc);
                            let _ = analyzer.add_if_err(res);
                            Ok(())
                        });
                    let _ = self.add_if_err(res);
                }
            }
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {
                tracing::trace!("parsing named revert");
                todo!("revert named args")
            }
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }
}
