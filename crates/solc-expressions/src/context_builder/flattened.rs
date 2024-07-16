use std::collections::BTreeMap;

use crate::{
    context_builder::ContextBuilder,
    func_call::{func_caller::FuncCaller, internal_call::InternalFuncCaller, intrinsic_call::*},
    ExprTyParser,
};
use graph::{
    elem::{Elem, RangeOp},
    nodes::{
        Builtin, Concrete, Context, ContextNode, ContextVar, ContextVarNode, ContractNode, ExprRet,
        FunctionNode, KilledKind, StructNode, SubContextKind,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, TypeNode, VarType,
};

use shared::{string_to_static, ExprErr, ExprFlag, FlatExpr, IntoExprErr, NodeIdx, RangeArena};
use solang_parser::pt::{CodeLocation, Expression, Loc, Statement};

impl<T> Flatten for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
}

#[derive(Debug, Copy, Clone)]
pub enum FuncOrCtx {
    Func(FunctionNode),
    Ctx(ContextNode),
}

impl From<FunctionNode> for FuncOrCtx {
    fn from(f: FunctionNode) -> Self {
        FuncOrCtx::Func(f)
    }
}

impl From<ContextNode> for FuncOrCtx {
    fn from(ctx: ContextNode) -> Self {
        FuncOrCtx::Ctx(ctx)
    }
}

pub trait Flatten:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
    fn traverse_statement(&mut self, stmt: &Statement, unchecked: Option<bool>) {
        use Statement::*;

        match stmt {
            Block {
                loc: _,
                unchecked,
                statements,
            } => {
                for statement in statements {
                    self.traverse_statement(statement, Some(*unchecked));
                }
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let lhs = var_decl.ty.clone();
                if let Some(rhs) = maybe_expr {
                    self.traverse_expression(rhs, unchecked);
                }
                self.traverse_expression(&lhs, unchecked);
                if let Some(name) = var_decl.name.clone() {
                    self.push_expr(FlatExpr::VarDef(
                        *loc,
                        Some(string_to_static(name.name)),
                        var_decl.storage.clone().map(Into::into),
                        maybe_expr.is_some(),
                    ));
                } else {
                    self.push_expr(FlatExpr::VarDef(
                        *loc,
                        None,
                        var_decl.storage.clone().map(Into::into),
                        maybe_expr.is_some(),
                    ));
                }
            }
            Args(_loc, _args) => {}
            If(loc, if_expr, true_body, maybe_false_body) => {
                // 1. Add conditional expressions
                // 2. Remove added conditional expressions
                // 3. Clone and negate for false side
                // 4. Add true body expressions
                // 5. Remove true body expressions
                // 6. Add false body expressions
                // 7. Remove false body expressions
                // 8. construct an `If` that lets the intepreter jump to each
                // based on their size
                let start_len = self.expr_stack_mut().len();
                self.traverse_expression(if_expr, unchecked);
                let true_cond = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                let mut false_cond = true_cond.clone();
                false_cond.push(FlatExpr::Not(if_expr.loc()));

                let true_cond_delta = true_cond.len();
                let false_cond_delta = false_cond.len();

                self.traverse_statement(true_body, unchecked);
                let true_body = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                let true_body_delta = true_body.len();

                let (if_expr, false_body) = if let Some(false_body) = maybe_false_body {
                    self.traverse_statement(false_body, unchecked);
                    let false_body = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                    let false_body_delta = false_body.len();
                    (
                        FlatExpr::If {
                            loc: *loc,
                            true_cond: true_cond_delta,
                            false_cond: false_cond_delta,
                            true_body: true_body_delta,
                            false_body: false_body_delta,
                        },
                        false_body,
                    )
                } else {
                    (
                        FlatExpr::If {
                            loc: *loc,
                            true_cond: true_cond_delta,
                            false_cond: false_cond_delta,
                            true_body: true_body_delta,
                            false_body: 0,
                        },
                        vec![],
                    )
                };

                self.push_expr(if_expr);
                let stack = self.expr_stack_mut();
                stack.extend(true_cond);
                stack.extend(false_cond);
                stack.extend(true_body);
                stack.extend(false_body);
            }
            While(loc, cond, body) => {}
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {}
            DoWhile(loc, while_stmt, while_expr) => {}
            Expression(loc, expr) => {
                self.traverse_expression(&expr, unchecked);
            }
            Continue(loc) => {
                self.push_expr(FlatExpr::Continue(*loc));
            }
            Break(loc) => {
                self.push_expr(FlatExpr::Break(*loc));
            }
            Assembly {
                loc,
                dialect: _,
                flags: _,
                block: yul_block,
            } => {}
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    self.traverse_expression(ret_expr, unchecked);
                }

                self.push_expr(FlatExpr::Return(*loc, maybe_ret_expr.is_some()));
            }
            Revert(loc, _maybe_err_path, _exprs) => {}
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {}
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }

    fn traverse_expression(&mut self, parent_expr: &Expression, unchecked: Option<bool>) {
        use Expression::*;

        match parent_expr {
            // literals
            NumberLiteral(..)
            | AddressLiteral(..)
            | StringLiteral(..)
            | BoolLiteral(..)
            | HexNumberLiteral(..)
            | HexLiteral(..)
            | RationalNumberLiteral(..)
            | Variable(..) => {
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }

            Negate(_loc, expr)
            | UnaryPlus(_loc, expr)
            | BitwiseNot(_loc, expr)
            | Not(_loc, expr)
            | Delete(_loc, expr)
            | Parenthesis(_loc, expr)
            | PreIncrement(_loc, expr)
            | PostIncrement(_loc, expr)
            | PreDecrement(_loc, expr)
            | PostDecrement(_loc, expr) => {
                self.traverse_expression(expr, unchecked);
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }

            New(new_loc, expr) => {
                match &**expr {
                    FunctionCall(func_loc, func_expr, input_exprs) => {
                        input_exprs.iter().rev().for_each(|expr| {
                            self.traverse_expression(expr, unchecked);
                        });

                        self.traverse_expression(func_expr, unchecked);
                        self.push_expr(FlatExpr::New(*new_loc));
                        self.push_expr(FlatExpr::FunctionCall(*func_loc, input_exprs.len()));
                    }
                    NamedFunctionCall(loc, func_expr, input_args) => {
                        input_args.iter().rev().for_each(|arg| {
                            self.traverse_expression(&arg.expr, unchecked);
                        });

                        self.traverse_expression(func_expr, unchecked);
                        self.push_expr(FlatExpr::New(*new_loc));
                        input_args.iter().for_each(|arg| {
                            self.push_expr(FlatExpr::from(arg));
                        });
                        self.push_expr(FlatExpr::NamedFunctionCall(*loc, input_args.len()));
                    }
                    _ => {
                        // add error
                        todo!()
                    }
                }
            }
            // Binary ops
            Power(_, lhs, rhs)
            | Add(_, lhs, rhs)
            | AssignAdd(_, lhs, rhs)
            | Subtract(_, lhs, rhs)
            | AssignSubtract(_, lhs, rhs)
            | Multiply(_, lhs, rhs)
            | AssignMultiply(_, lhs, rhs)
            | Divide(_, lhs, rhs)
            | AssignDivide(_, lhs, rhs) => {
                self.traverse_expression(rhs, unchecked);
                self.traverse_expression(lhs, unchecked);
                let parent = match parent_expr {
                    Power(loc, ..) => FlatExpr::Power(*loc, unchecked.unwrap_or(false)),
                    Add(loc, ..) => FlatExpr::Add(*loc, unchecked.unwrap_or(false)),
                    AssignAdd(loc, ..) => FlatExpr::AssignAdd(*loc, unchecked.unwrap_or(false)),
                    Subtract(loc, ..) => FlatExpr::Subtract(*loc, unchecked.unwrap_or(false)),
                    AssignSubtract(loc, ..) => {
                        FlatExpr::AssignSubtract(*loc, unchecked.unwrap_or(false))
                    }
                    Multiply(loc, ..) => FlatExpr::Multiply(*loc, unchecked.unwrap_or(false)),
                    AssignMultiply(loc, ..) => {
                        FlatExpr::AssignMultiply(*loc, unchecked.unwrap_or(false))
                    }
                    Divide(loc, ..) => FlatExpr::Divide(*loc, unchecked.unwrap_or(false)),
                    AssignDivide(loc, ..) => {
                        FlatExpr::AssignDivide(*loc, unchecked.unwrap_or(false))
                    }
                    _ => unreachable!(),
                };

                self.push_expr(parent);
            }

            Modulo(_, lhs, rhs)
            | AssignModulo(_, lhs, rhs)
            | ShiftLeft(_, lhs, rhs)
            | AssignShiftLeft(_, lhs, rhs)
            | ShiftRight(_, lhs, rhs)
            | AssignShiftRight(_, lhs, rhs)
            | BitwiseAnd(_, lhs, rhs)
            | AssignAnd(_, lhs, rhs)
            | BitwiseXor(_, lhs, rhs)
            | AssignXor(_, lhs, rhs)
            | BitwiseOr(_, lhs, rhs)
            | AssignOr(_, lhs, rhs)
            | Assign(_, lhs, rhs)
            | Equal(_, lhs, rhs)
            | NotEqual(_, lhs, rhs)
            | Less(_, lhs, rhs)
            | More(_, lhs, rhs)
            | LessEqual(_, lhs, rhs)
            | MoreEqual(_, lhs, rhs)
            | And(_, lhs, rhs)
            | Or(_, lhs, rhs) => {
                self.traverse_expression(rhs, unchecked);
                self.traverse_expression(lhs, unchecked);
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }

            List(_, params) => {
                params.iter().for_each(|(loc, maybe_param)| {
                    if let Some(param) = maybe_param {
                        self.traverse_expression(&param.ty, unchecked);
                    } else {
                        self.push_expr(FlatExpr::Null(*loc));
                    }
                });
                params.iter().for_each(|(loc, maybe_param)| {
                    if let Some(param) = maybe_param {
                        if let Some(name) = &param.name {
                            self.push_expr(FlatExpr::Parameter(
                                param.loc,
                                param.storage.clone().map(Into::into),
                                Some(Box::leak(name.name.clone().into_boxed_str())),
                            ));
                        } else {
                            self.push_expr(FlatExpr::Parameter(
                                param.loc,
                                param.storage.clone().map(Into::into),
                                None,
                            ));
                        }
                    } else {
                        self.push_expr(FlatExpr::Parameter(*loc, None, None));
                    }
                });
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }
            // array
            ArraySubscript(loc, ty_expr, None) => {
                self.traverse_expression(ty_expr, unchecked);
                self.push_expr(FlatExpr::ArrayTy(*loc));
            }
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.traverse_expression(index_expr, unchecked);
                self.traverse_expression(ty_expr, unchecked);
                self.push_expr(FlatExpr::ArrayIndexAccess(*loc));
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {}
            ArraySlice(loc, lhs_expr, maybe_middle_expr, maybe_rhs) => {}
            ArrayLiteral(loc, _) => {}

            // Function calls
            FunctionCallBlock(loc, func_expr, call_block) => {
                self.traverse_statement(call_block, unchecked);
                self.traverse_expression(func_expr, unchecked);
                self.push_expr(FlatExpr::FunctionCallBlock(*loc));
            }
            NamedFunctionCall(loc, func_expr, input_args) => {
                input_args.iter().rev().for_each(|arg| {
                    self.traverse_expression(&arg.expr, unchecked);
                });

                self.push_expr(FlatExpr::FunctionCallName(input_args.len()));
                self.traverse_expression(func_expr, unchecked);
                input_args.iter().for_each(|arg| {
                    self.push_expr(FlatExpr::from(arg));
                });
                self.push_expr(FlatExpr::NamedFunctionCall(*loc, input_args.len()));
            }
            FunctionCall(loc, func_expr, input_exprs) => {
                input_exprs.iter().rev().for_each(|expr| {
                    self.traverse_expression(expr, unchecked);
                });

                self.push_expr(FlatExpr::FunctionCallName(input_exprs.len()));
                self.traverse_expression(func_expr, unchecked);
                self.push_expr(FlatExpr::FunctionCall(*loc, input_exprs.len()));
            }
            // member
            This(loc) => self.push_expr(FlatExpr::This(*loc)),
            MemberAccess(loc, member_expr, ident) => {
                self.traverse_expression(member_expr, unchecked);
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }

            // Misc.
            Type(..) => self.push_expr(FlatExpr::try_from(parent_expr).unwrap()),
        }
    }

    fn interpret(
        &mut self,
        func_or_ctx: impl Into<FuncOrCtx>,
        body_loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        let stack = std::mem::take(self.expr_stack_mut());
        tracing::trace!("stack: {stack:#?}");
        let foc: FuncOrCtx = func_or_ctx.into();

        let ctx = match foc {
            FuncOrCtx::Func(func) => {
                let raw_ctx = Context::new(
                    func,
                    self.add_if_err(func.name(self).into_expr_err(body_loc))
                        .unwrap(),
                    body_loc,
                );
                let ctx = ContextNode::from(self.add_node(Node::Context(raw_ctx)));
                self.add_edge(ctx, func, Edge::Context(ContextEdge::Context));

                let res = func.add_params_to_ctx(ctx, self).into_expr_err(body_loc);
                self.add_if_err(res);
                ctx
            }
            FuncOrCtx::Ctx(ctx) => ctx,
        };

        while (!ctx.is_ended(self).unwrap() || !ctx.live_edges(self).unwrap().is_empty())
            && ctx.parse_idx(self) < stack.len()
        {
            let res = self.interpret_step(arena, ctx, body_loc, &stack[..]);
            self.add_if_err(res);
        }
    }

    fn interpret_step(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        body_loc: Loc,
        stack: &[FlatExpr],
    ) -> Result<(), ExprErr> {
        self.flat_apply_to_edges(
            ctx,
            body_loc,
            arena,
            stack,
            &|analyzer: &mut Self,
              arena: &mut RangeArena<Elem<Concrete>>,
              ctx: ContextNode,
              _: Loc,
              stack: &[FlatExpr]| { analyzer.interpret_expr(arena, ctx, stack) },
        )
    }

    fn interpret_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &[FlatExpr],
    ) -> Result<(), ExprErr> {
        use FlatExpr::*;

        if ctx.is_killed(self).unwrap() {
            return Ok(());
        }

        let parse_idx = ctx.increment_parse_idx(self);
        let kill_after_exec = parse_idx == stack.len().saturating_sub(1);
        let Some(next) = stack.get(parse_idx) else {
            let loc = stack
                .last()
                .map(|l| l.try_loc())
                .flatten()
                .unwrap_or(Loc::Implicit);
            return ctx.kill(self, loc, KilledKind::Ended).into_expr_err(loc);
        };
        let next = *next;

        tracing::trace!(
            "parsing {:?} in context {} - flag: {:?}",
            next,
            ctx.path(self),
            self.peek_expr_flag()
        );
        match next {
            // Flag expressions
            FunctionCallName(n) => {
                self.set_expr_flag(ExprFlag::FunctionName(n));
                Ok(())
            }
            Negate(_) => {
                self.set_expr_flag(ExprFlag::Negate);
                Ok(())
            }
            New(_) => {
                self.set_expr_flag(ExprFlag::New);
                Ok(())
            }

            // Literals
            AddressLiteral(loc, lit) => self.address_literal(ctx, loc, lit),
            StringLiteral(loc, lit) => self.string_literal(ctx, loc, lit),
            BoolLiteral(loc, b) => self.bool_literal(ctx, loc, b),
            HexLiteral(loc, hex) => self.hex_literals(ctx, loc, hex),
            NumberLiteral(..) | HexNumberLiteral(..) | RationalNumberLiteral(..) => {
                self.interp_negatable_literal(arena, ctx, next)
            }

            VarDef(..) => self.interp_var_def(arena, ctx, next),
            Type(..) => self.interp_type(arena, ctx, next),
            Return(..) => self.interp_return(arena, ctx, next),
            Variable(..) => self.interp_var(arena, ctx, next),
            Assign(..) => self.interp_assign(arena, ctx, next),

            Not(..) => self.interp_not(arena, ctx, next),

            // Comparator
            Equal(loc) | NotEqual(loc) | Less(loc) | More(loc) | LessEqual(loc)
            | MoreEqual(loc) => self.interp_cmp(arena, ctx, loc, next),

            If { .. } => self.interp_if(arena, ctx, stack, next),

            Continue(loc) | Break(loc) => Err(ExprErr::Todo(
                loc,
                "Control flow expressions like break and continue are not currently supported"
                    .to_string(),
            )),

            PostIncrement(loc, ..)
            | PreIncrement(loc, ..)
            | PostDecrement(loc, ..)
            | PreDecrement(loc, ..) => self.interp_xxcrement(arena, ctx, next, loc),

            ArrayTy(..) => self.interp_array_ty(arena, ctx, next),
            ArrayIndexAccess(_) => todo!(),
            ArraySlice(_) => todo!(),
            ArrayLiteral(_) => todo!(),

            Power(loc, ..)
            | Multiply(loc, ..)
            | Divide(loc, ..)
            | Modulo(loc, ..)
            | Add(loc, ..)
            | Subtract(loc, ..)
            | ShiftLeft(loc, ..)
            | ShiftRight(loc, ..)
            | BitwiseAnd(loc, ..)
            | BitwiseXor(loc, ..)
            | BitwiseOr(loc, ..)
            | BitwiseNot(loc, ..) => self.interp_op(arena, ctx, next, loc, false),

            AssignAdd(loc, ..)
            | AssignSubtract(loc, ..)
            | AssignMultiply(loc, ..)
            | AssignDivide(loc, ..)
            | AssignModulo(loc, ..)
            | AssignOr(loc, ..)
            | AssignAnd(loc, ..)
            | AssignXor(loc, ..)
            | AssignShiftLeft(loc, ..)
            | AssignShiftRight(loc, ..) => self.interp_op(arena, ctx, next, loc, true),

            Parenthesis(_) => todo!(),
            MemberAccess(..) => todo!(),

            FunctionCall(..) => self.interp_func_call(arena, ctx, next, None),
            FunctionCallBlock(_) => todo!(),
            NamedArgument(..) => Ok(()),
            NamedFunctionCall(..) => {
                self.interp_named_func_call(arena, ctx, stack, next, parse_idx)
            }

            Delete(_) => todo!(),
            UnaryPlus(_) => todo!(),

            And(_) => todo!(),
            Or(_) => todo!(),
            ConditionalOperator(_) => todo!(),

            This(_) => todo!(),
            List(_, _) => self.interp_list(arena, ctx, stack, next, parse_idx),
            Parameter(_, _, _) => Ok(()),
            Null(loc) => ctx.push_expr(ExprRet::Null, self).into_expr_err(loc),
        }
    }

    fn interp_list(
        &mut self,
        _arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &[FlatExpr],
        list: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::List(loc, n) = list else {
            unreachable!()
        };

        let param_names_start = parse_idx.saturating_sub(n);
        let params = &stack[param_names_start..parse_idx];
        let mut values = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
        values.reverse();
        values
            .into_iter()
            .zip(params)
            .try_for_each(|(ret, param)| {
                let res = self.list_inner(ctx, *param, ret, loc)?;
                ctx.push_expr(res, self).into_expr_err(loc)
            })?;

        let new_values = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
        ctx.push_expr(ExprRet::Multi(new_values), self)
            .into_expr_err(loc)?;
        ctx.debug_expr_stack(self).unwrap();
        Ok(())
    }

    fn interp_xxcrement(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        let (pre, increment) = match next {
            FlatExpr::PreIncrement(_) => (true, true),
            FlatExpr::PostIncrement(_) => (false, true),
            FlatExpr::PreDecrement(_) => (true, false),
            FlatExpr::PostDecrement(_) => (false, false),
            _ => unreachable!(),
        };

        let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
        let [var] = into_sized(res);
        self.match_in_de_crement(arena, ctx, pre, increment, loc, &var)
    }

    fn interp_op(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
        loc: Loc,
        assign: bool,
    ) -> Result<(), ExprErr> {
        let op = RangeOp::try_from(next).unwrap();
        let res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
        let [lhs, rhs] = into_sized(res);
        self.op_match(arena, ctx, loc, &lhs, &rhs, op, assign)
    }

    fn interp_if(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &[FlatExpr],
        if_expr: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::If {
            loc,
            true_cond,
            false_cond,
            true_body,
            false_body,
        } = if_expr
        else {
            unreachable!()
        };

        let true_subctx_kind = SubContextKind::new_fork(ctx, true);
        let tctx = Context::new_subctx(true_subctx_kind, loc, self, None).into_expr_err(loc)?;
        let true_subctx = ContextNode::from(self.add_node(Node::Context(tctx)));

        let false_subctx_kind = SubContextKind::new_fork(ctx, false);
        let fctx = Context::new_subctx(false_subctx_kind, loc, self, None).into_expr_err(loc)?;
        let false_subctx = ContextNode::from(self.add_node(Node::Context(fctx)));
        ctx.set_child_fork(true_subctx, false_subctx, self)
            .into_expr_err(loc)?;
        let ctx_fork = self.add_node(Node::ContextFork);
        self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::ContextFork));
        self.add_edge(
            NodeIdx::from(true_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );
        self.add_edge(
            NodeIdx::from(false_subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );

        // parse the true condition expressions
        for i in 0..true_cond {
            self.interpret_step(arena, true_subctx, loc, stack)?;
        }
        // skip the false condition expressions
        true_subctx.skip_n_exprs(false_cond, self);

        // skip the true condition expressions
        false_subctx.skip_n_exprs(true_cond, self);
        // parse the false condition expressions
        for i in 0..false_cond {
            self.interpret_step(arena, false_subctx, loc, stack)?;
        }

        // todo: the kill check
        for i in 0..true_body {
            self.interpret_step(arena, true_subctx, loc, stack)?;
        }
        // skip the false condition expressions
        true_subctx.skip_n_exprs(false_body, self);

        // skip the true body expressions
        false_subctx.skip_n_exprs(true_body, self);
        // parse the false body expressions
        for i in 0..false_body {
            self.interpret_step(arena, false_subctx, loc, stack)?;
        }
        Ok(())
    }

    fn interp_cmp(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        cmp: FlatExpr,
    ) -> Result<(), ExprErr> {
        let res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
        let [lhs, rhs] = into_sized::<ExprRet, 2>(res);

        match cmp {
            FlatExpr::Equal(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Eq, &rhs),
            FlatExpr::NotEqual(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Neq, &rhs),
            FlatExpr::Less(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Lt, &rhs),
            FlatExpr::More(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Gt, &rhs),
            FlatExpr::LessEqual(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Lte, &rhs),
            FlatExpr::MoreEqual(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Gte, &rhs),
            _ => unreachable!(),
        }
    }

    fn interp_not(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        not: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Not(loc) = not else {
            unreachable!()
        };

        let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
        let [inner] = into_sized::<ExprRet, 1>(res);

        self.not_inner(arena, ctx, loc, inner.flatten())
    }

    fn interp_var_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        var_def: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::VarDef(loc, maybe_name, maybe_storage, inited) = var_def else {
            unreachable!()
        };

        let lhs_ty;
        let mut rhs = None;

        if inited {
            let res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
            let [lhs_res, rhs_res] = into_sized::<ExprRet, 2>(res);
            lhs_ty = Some(lhs_res);
            rhs = Some(rhs_res);
        } else {
            let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            let [lhs_res] = into_sized::<ExprRet, 1>(res);
            lhs_ty = Some(lhs_res);
        }
        if let Some(lhs_ty) = lhs_ty {
            let _ = self.match_var_def(
                arena,
                ctx,
                (maybe_name, maybe_storage),
                loc,
                &lhs_ty,
                rhs.as_ref(),
            )?;
            Ok(())
        } else {
            Err(ExprErr::NoLhs(
                loc,
                "Variable defintion had no left hand side".to_string(),
            ))
        }
    }

    fn interp_type(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        ty: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Type(loc, ty) = ty else {
            unreachable!()
        };

        if matches!(self.peek_expr_flag(), Some(ExprFlag::FunctionName(..))) {
            self.take_expr_flag();
        }

        if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self, arena) {
            if let Some(idx) = self.builtins().get(&builtin) {
                ctx.push_expr(ExprRet::Single(*idx), self)
                    .into_expr_err(loc)
            } else {
                let idx = self.add_node(Node::Builtin(builtin.clone()));
                self.builtins_mut().insert(builtin, idx);
                ctx.push_expr(ExprRet::Single(idx), self).into_expr_err(loc)
            }
        } else {
            ctx.push_expr(ExprRet::Null, self).into_expr_err(loc)
        }
    }

    fn interp_return(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        ret: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Return(loc, nonempty) = ret else {
            unreachable!()
        };
        if nonempty {
            let ret = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            self.return_match(arena, ctx, &loc, ret.first().unwrap(), 0);
            Ok(())
        } else {
            self.return_match(arena, ctx, &loc, &ExprRet::Null, 0);
            ctx.kill(self, loc, KilledKind::Ended).into_expr_err(loc)
        }
    }

    fn interp_var(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        var: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Variable(loc, name) = var else {
            unreachable!()
        };

        match self.take_expr_flag() {
            Some(ExprFlag::FunctionName(n)) => {
                let maybe_fn = self
                    .find_func(arena, ctx, name.to_string(), n)
                    .into_expr_err(loc)?;

                if let Some(fn_node) = maybe_fn {
                    let as_var = ContextVar::maybe_from_user_ty(self, loc, fn_node.into()).unwrap();
                    let fn_var = ContextVarNode::from(self.add_node(as_var));
                    ctx.add_var(fn_var, self).into_expr_err(loc)?;
                    self.add_edge(fn_var, ctx, Edge::Context(ContextEdge::Variable));
                    return ctx
                        .push_expr(ExprRet::Single(fn_var.into()), self)
                        .into_expr_err(loc);
                }
            }
            Some(other) => {
                self.set_expr_flag(other);
            }
            _ => {}
        }
        self.variable(
            arena,
            &solang_parser::pt::Identifier {
                loc,
                name: name.to_string(),
            },
            ctx,
            None,
            None,
        )
    }

    fn interp_assign(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        assign: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Assign(loc) = assign else {
            unreachable!()
        };

        let res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
        let [lhs, rhs] = into_sized(res);
        self.match_assign_sides(arena, ctx, loc, &lhs, &rhs)
    }

    fn interp_array_ty(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        arr_ty: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::ArrayTy(loc) = arr_ty else {
            unreachable!()
        };
        let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
        let [arr_ty] = into_sized(res);
        self.match_ty(ctx, loc, arr_ty)
    }

    fn interp_named_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &[FlatExpr],
        func_call: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::NamedFunctionCall(loc, n) = func_call else {
            unreachable!()
        };

        let names_start = parse_idx.saturating_sub(n);
        let names = stack[names_start..parse_idx]
            .iter()
            .map(|named_arg| {
                let FlatExpr::NamedArgument(_, name) = named_arg else {
                    unreachable!()
                };
                *name
            })
            .collect::<Vec<_>>();

        self.interp_func_call(arena, ctx, func_call, Some(names))
    }

    fn interp_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_call: FlatExpr,
        input_names: Option<Vec<&str>>,
    ) -> Result<(), ExprErr> {
        let (loc, n) = match func_call {
            FlatExpr::FunctionCall(loc, n) => (loc, n),
            FlatExpr::NamedFunctionCall(loc, n) => (loc, n),
            _ => unreachable!(),
        };

        let func_and_inputs = ctx
            .pop_n_latest_exprs(n + 1, loc, self)
            .into_expr_err(loc)?;

        let func = func_and_inputs
            .first()
            .unwrap()
            .expect_single()
            .into_expr_err(loc)?;

        let is_new_call = match self.peek_expr_flag() {
            Some(ExprFlag::New) => {
                let _ = self.take_expr_flag();
                true
            }
            _ => false,
        };

        func_and_inputs[1..].iter().for_each(|i| {
            println!("here: {}", i.debug_str(self));
        });

        // order the named inputs
        let inputs = if n > 0 {
            let res = if let Some(input_names) = input_names {
                let mut ret = Ok(None);
                let ordered_names = match self.node(func) {
                    Node::Function(..) => FunctionNode::from(func).ordered_param_names(self),
                    Node::Struct(..) => StructNode::from(func).ordered_new_param_names(self),
                    Node::Contract(..) => ContractNode::from(func).ordered_new_param_names(self),
                    _ => todo!(),
                };

                if ordered_names != input_names {
                    let mapping = ordered_names
                        .iter()
                        .enumerate()
                        .filter_map(|(i, n)| Some((input_names.iter().position(|k| k == n)?, i)))
                        .collect::<BTreeMap<_, _>>();
                    if mapping.len() != ordered_names.len() {
                        ret = Err(ExprErr::ParseError(
                            loc,
                            "Named arguments are incorrect".to_string(),
                        ));
                    } else {
                        let mut tmp_inputs = vec![];
                        tmp_inputs.resize(n, ExprRet::Null);
                        func_and_inputs[1..]
                            .iter()
                            .enumerate()
                            .for_each(|(i, ret)| {
                                let target_idx = mapping[&i];
                                tmp_inputs[target_idx] = ret.clone();
                            });
                        ret = Ok(Some(tmp_inputs));
                    }
                }
                ret
            } else {
                Ok(None)
            };
            res?.unwrap_or(func_and_inputs[1..].to_vec())
        } else {
            vec![]
        };

        let inputs = ExprRet::Multi(inputs);

        if is_new_call {
            return self.new_call_inner(arena, ctx, func, inputs, loc);
        }

        let ty = match self.node(func) {
            Node::ContextVar(..) => {
                let ty = ContextVarNode::from(func).ty(self).unwrap();
                ty.clone()
            }
            _ => VarType::try_from_idx(self, func).unwrap(),
        };

        match ty {
            VarType::User(TypeNode::Struct(s), _) => {
                self.construct_struct_inner(arena, ctx, s, inputs, loc)
            }
            VarType::User(TypeNode::Contract(s), _) => {
                unreachable!("should be unreachable: contract")
            }
            VarType::User(TypeNode::Func(s), _) => {
                if self.builtin_fn_nodes().iter().any(|(_, v)| *v == func) {
                    // its a builtin function call
                    todo!("builtin fn")
                } else {
                    self.func_call(arena, ctx, loc, &inputs, s, None, None)
                }
            }
            VarType::BuiltIn(bn, _) => {
                // cast to type
                let Node::Builtin(builtin) = self.node(bn).clone() else {
                    unreachable!()
                };
                self.cast_inner(arena, ctx, ty, &builtin, inputs, loc)
            }
            _ => todo!(),
        }
    }

    fn interp_negatable_literal(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lit: FlatExpr,
    ) -> Result<(), ExprErr> {
        let mut negate = false;
        match self.take_expr_flag() {
            Some(ExprFlag::Negate) => {
                negate = true;
            }
            Some(other) => self.set_expr_flag(other),
            _ => {}
        };

        match lit {
            FlatExpr::NumberLiteral(loc, int, exp, unit) => {
                self.number_literal(ctx, loc, int, exp, negate, unit)
            }
            FlatExpr::HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, loc, b, negate),
            FlatExpr::RationalNumberLiteral(loc, integer, fraction, exp, unit) => {
                self.rational_number_literal(arena, ctx, loc, integer, fraction, exp, unit, negate)
            }
            _ => unreachable!(),
        }
    }

    /// Apply an expression or statement to all *live* edges of a context. This is used everywhere
    /// to ensure we only ever update *live* contexts. If a context has a subcontext, we *never*
    /// want to update the original context. We only ever want to operate on the latest edges.
    fn flat_apply_to_edges(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
        stack: &[FlatExpr],
        closure: &impl Fn(
            &mut Self,
            &mut RangeArena<Elem<Concrete>>,
            ContextNode,
            Loc,
            &[FlatExpr],
        ) -> Result<(), ExprErr>,
    ) -> Result<(), ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        if !ctx.killed_or_ret(self).into_expr_err(loc)? {
            if ctx.underlying(self).into_expr_err(loc)?.child.is_some() {
                if live_edges.is_empty() {
                    Ok(())
                } else {
                    live_edges
                        .iter()
                        .try_for_each(|ctx| closure(self, arena, *ctx, loc, stack))
                }
            } else if live_edges.is_empty() {
                closure(self, arena, ctx, loc, stack)
            } else {
                live_edges
                    .iter()
                    .try_for_each(|ctx| closure(self, arena, *ctx, loc, stack))
            }
        } else {
            Ok(())
        }
    }
}

fn into_sized<T, const N: usize>(v: Vec<T>) -> [T; N] {
    v.try_into()
        .unwrap_or_else(|v: Vec<T>| panic!("Expected a Vec of length {} but it was {}", N, v.len()))
}
