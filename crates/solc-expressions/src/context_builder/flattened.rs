use crate::yul::YulFuncCaller;
use std::collections::BTreeMap;

use crate::{
    context_builder::ContextBuilder,
    func_call::{func_caller::FuncCaller, internal_call::InternalFuncCaller, intrinsic_call::*},
    ExprTyParser,
};
use graph::{
    elem::{Elem, RangeOp},
    nodes::{
        Builtin, Concrete, ConcreteNode, Context, ContextNode, ContextVar, ContextVarNode,
        ContractNode, ExprRet, FunctionNode, KilledKind, StructNode, SubContextKind, YulFunction,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, TypeNode, VarType,
};

use shared::{
    post_to_site, string_to_static, ElseOrDefault, ExprErr, ExprFlag, FlatExpr, FlatYulExpr,
    GraphError, GraphLike, IfElseChain, IntoExprErr, NodeIdx, RangeArena, USE_DEBUG_SITE,
};
use solang_parser::pt::{
    CodeLocation, Expression, Identifier, Loc, Statement, YulExpression, YulStatement,
};

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
                let cmp = self.expr_stack_mut().pop().unwrap();
                // have it be a require statement
                self.push_expr(FlatExpr::Requirement(*loc));
                self.push_expr(cmp);
                let true_cond = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();

                // the false condition is the same as the true, but with the comparator inverted
                let mut false_cond = true_cond.clone();
                if let Some(last) = false_cond.pop() {
                    false_cond.push(last.try_inv_cmp().unwrap_or(FlatExpr::Not(*loc)));
                }

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
            } => {
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulStartBlock));
                self.traverse_yul_statement(&YulStatement::Block(yul_block.clone()));
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulEndBlock));
            }
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

    fn traverse_yul_statement(&mut self, stmt: &YulStatement) {
        use YulStatement::*;
        match stmt {
            Assign(loc, lhs, rhs) => {
                self.traverse_yul_expression(rhs);
                lhs.iter().for_each(|l| {
                    self.traverse_yul_expression(l);
                });
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulAssign(*loc, lhs.len())));
            }
            VariableDeclaration(loc, idents, maybe_assignment) => {
                if let Some(rhs) = maybe_assignment {
                    self.traverse_yul_expression(rhs);
                }
                let uint: &'static solang_parser::pt::Type =
                    Box::leak(Box::new(solang_parser::pt::Type::Uint(256)));

                idents.iter().for_each(|ident| {
                    // NOTE: for now yul does not support
                    // user types. but they may in the future
                    self.push_expr(FlatExpr::Type(ident.loc, uint));
                    self.push_expr(FlatExpr::VarDef(
                        *loc,
                        Some(string_to_static(ident.id.name.clone())),
                        None,
                        false,
                    ));
                });
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulVarDecl(
                    *loc,
                    idents.len(),
                    maybe_assignment.is_some(),
                )));
            }
            If(loc, if_expr, true_stmt) => {
                let iec = IfElseChain {
                    if_expr: if_expr.clone(),
                    true_stmt: YulStatement::Block(true_stmt.clone()),
                    next: None,
                };
                self.traverse_yul_if_else(*loc, iec);
            }
            For(yul_for) => {}
            Switch(solang_parser::pt::YulSwitch {
                loc,
                condition,
                cases,
                default,
            }) => {
                if let Some(iec) = self.add_if_err(IfElseChain::from(
                    *loc,
                    (condition.clone(), cases.clone(), default.clone()),
                )) {
                    self.traverse_yul_if_else(*loc, iec);
                }
            }
            Leave(loc) => {
                self.push_expr(FlatExpr::Break(*loc));
            }
            Break(loc) => {
                self.push_expr(FlatExpr::Break(*loc));
            }
            Continue(loc) => {
                self.push_expr(FlatExpr::Continue(*loc));
            }
            Block(block) => {
                for statement in block.statements.iter() {
                    self.traverse_yul_statement(statement);
                }
            }
            FunctionDefinition(def) => {
                let start_len = self.expr_stack().len();
                let inputs_as_var_decl =
                    YulStatement::VariableDeclaration(def.loc, def.params.clone(), None);
                self.traverse_yul_statement(&inputs_as_var_decl);

                def.params.iter().for_each(|param| {
                    self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulVariable(
                        param.loc,
                        string_to_static(param.id.name.clone()),
                    )))
                });

                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulAssign(
                    def.loc,
                    def.params.len(),
                )));
                let rets_as_var_decl =
                    YulStatement::VariableDeclaration(def.loc, def.returns.clone(), None);
                self.traverse_yul_statement(&rets_as_var_decl);

                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulStartBlock));
                for stmt in def.body.statements.iter() {
                    self.traverse_yul_statement(stmt);
                }
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulEndBlock));

                let func = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();

                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulFuncDef(
                    def.loc,
                    string_to_static(def.id.name.clone()),
                    func.len(),
                )));
                self.expr_stack_mut().extend(func);
            }
            FunctionCall(call) => {
                self.traverse_yul_expression(&YulExpression::FunctionCall(call.clone()));
            }
            Error(loc) => {}
        }
    }

    fn traverse_yul_if_else(&mut self, loc: Loc, iec: IfElseChain) {
        let true_body = &iec.true_stmt;
        let start_len = self.expr_stack_mut().len();
        self.push_expr(FlatExpr::NumberLiteral(loc, "0", "", None));
        self.traverse_yul_expression(&iec.if_expr);

        // have it be a require statement
        self.push_expr(FlatExpr::Requirement(loc));
        self.push_expr(FlatExpr::More(loc));

        let true_cond = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();

        // the false condition is the same as the true, but with the comparator inverted
        let mut false_cond = true_cond.clone();
        let _ = false_cond.pop();
        false_cond.push(FlatExpr::Equal(loc));

        let true_cond_delta = true_cond.len();
        let false_cond_delta = false_cond.len();

        self.traverse_yul_statement(true_body);
        let true_body = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
        let true_body_delta = true_body.len();

        let (if_expr, false_body) = if let Some(next) = iec.next {
            match next {
                ElseOrDefault::Else(curr) => {
                    self.traverse_yul_if_else(loc, *curr);
                }
                ElseOrDefault::Default(false_body) => self.traverse_yul_statement(&false_body),
            }
            let false_body = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
            let false_body_delta = false_body.len();
            (
                FlatExpr::If {
                    loc,
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
                    loc,
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

    fn traverse_yul_expression(&mut self, expr: &YulExpression) {
        use YulExpression::*;
        match expr {
            FunctionCall(func_call) => {
                func_call.arguments.iter().rev().for_each(|expr| {
                    self.traverse_yul_expression(expr);
                });

                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulFuncCall(
                    expr.loc(),
                    string_to_static(func_call.id.name.clone()),
                    func_call.arguments.len(),
                )));
            }
            SuffixAccess(_, member, _) => {
                self.traverse_yul_expression(member);
                self.push_expr(FlatExpr::try_from(expr).unwrap());
            }
            _ => self.push_expr(FlatExpr::try_from(expr).unwrap()),
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

            Negate(_loc, expr) => {
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
                self.traverse_expression(expr, unchecked);
            }

            Parenthesis(_loc, expr) => self.traverse_expression(expr, unchecked),

            UnaryPlus(_loc, expr)
            | BitwiseNot(_loc, expr)
            | Not(_loc, expr)
            | Delete(_loc, expr)
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

                self.traverse_expression(func_expr, unchecked);
                match self.expr_stack_mut().pop().unwrap() {
                    FlatExpr::Super(loc, name) => {
                        self.push_expr(FlatExpr::FunctionCallName(input_args.len(), true, true));
                        self.push_expr(FlatExpr::Variable(loc, name));
                    }
                    other => {
                        self.push_expr(FlatExpr::FunctionCallName(input_args.len(), false, true));
                        self.push_expr(other);
                    }
                }

                input_args.iter().for_each(|arg| {
                    self.push_expr(FlatExpr::from(arg));
                });
                self.push_expr(FlatExpr::NamedFunctionCall(*loc, input_args.len()));
            }
            FunctionCall(loc, func_expr, input_exprs) => match &**func_expr {
                Variable(Identifier { name, .. }) if matches!(&**name, "require" | "assert") => {
                    input_exprs.iter().rev().for_each(|expr| {
                        self.traverse_expression(expr, unchecked);
                    });
                    let cmp = self.expr_stack_mut().pop().unwrap();
                    self.push_expr(FlatExpr::Requirement(*loc));
                    self.push_expr(cmp);
                }
                _ => {
                    input_exprs.iter().rev().for_each(|expr| {
                        self.traverse_expression(expr, unchecked);
                    });

                    self.traverse_expression(func_expr, unchecked);
                    match self.expr_stack_mut().pop().unwrap() {
                        FlatExpr::Super(loc, name) => {
                            self.push_expr(FlatExpr::FunctionCallName(
                                input_exprs.len(),
                                true,
                                false,
                            ));
                            self.push_expr(FlatExpr::Variable(loc, name));
                        }
                        other => {
                            self.push_expr(FlatExpr::FunctionCallName(
                                input_exprs.len(),
                                false,
                                false,
                            ));
                            self.push_expr(other);
                        }
                    }

                    self.push_expr(FlatExpr::FunctionCall(*loc, input_exprs.len()));
                }
            },
            // member
            This(loc) => self.push_expr(FlatExpr::This(*loc)),
            MemberAccess(loc, member_expr, ident) => match &**member_expr {
                Variable(Identifier { name, .. }) if name == "super" => {
                    self.push_expr(FlatExpr::Super(*loc, string_to_static(ident)));
                }
                _ => {
                    self.traverse_expression(member_expr, unchecked);
                    self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
                }
            },

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
        let mut stack = std::mem::take(self.expr_stack_mut());
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
            let res = self.interpret_step(arena, ctx, body_loc, &mut stack);
            if unsafe { USE_DEBUG_SITE } {
                post_to_site(&*self, arena);
            }
            self.add_if_err(res);
        }
    }

    fn interpret_step(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        body_loc: Loc,
        stack: &mut Vec<FlatExpr>,
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
              stack: &mut Vec<FlatExpr>| {
                analyzer.interpret_expr(arena, ctx, stack)
            },
        )
    }

    fn interpret_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
    ) -> Result<(), ExprErr> {
        use FlatExpr::*;

        if ctx.is_killed(self).unwrap() {
            return Ok(());
        }

        let parse_idx = ctx.increment_parse_idx(self);
        let Some(next) = stack.get(parse_idx) else {
            let mut loc = None;
            let mut stack_rev_iter = stack.iter().rev();
            let mut loccer = stack_rev_iter.next();
            while loc.is_none() && loccer.is_some() {
                loc = loccer.unwrap().try_loc();
                loccer = stack_rev_iter.next();
            }
            let loc = loc.unwrap_or(Loc::Implicit);
            return ctx.kill(self, loc, KilledKind::Ended).into_expr_err(loc);
        };
        let next = *next;

        tracing::trace!(
            "parsing (idx: {parse_idx}) {:?} in context {} - flag: {:?}",
            next,
            ctx.path(self),
            self.peek_expr_flag()
        );

        match next {
            // Flag expressions
            FunctionCallName(n, is_super, named_args) => {
                self.set_expr_flag(ExprFlag::FunctionName(n, is_super, named_args));
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
            Variable(..) => self.interp_var(arena, ctx, stack, next, parse_idx),
            Assign(..) => self.interp_assign(arena, ctx, next),

            Not(..) => self.interp_not(arena, ctx, next),

            // Comparator
            Equal(loc) | NotEqual(loc) | Less(loc) | More(loc) | LessEqual(loc)
            | MoreEqual(loc) | And(loc) | Or(loc) => self.interp_cmp(arena, ctx, loc, next),

            If { .. } => self.interp_if(arena, ctx, stack, next, parse_idx),

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
            ArrayIndexAccess(_) => self.interp_array_idx(arena, ctx, next),
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
            | BitwiseOr(loc, ..) => self.interp_op(arena, ctx, next, loc, false),

            BitwiseNot(loc, ..) => self.interp_bit_not(arena, ctx, next),

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

            Super(..) => unreachable!(),
            MemberAccess(..) => self.interp_member_access(arena, ctx, next),

            Requirement(..) => {
                self.set_expr_flag(ExprFlag::Requirement);
                Ok(())
            }
            FunctionCall(..) => self.interp_func_call(arena, ctx, next, None),
            FunctionCallBlock(_) => todo!(),
            NamedArgument(..) => Ok(()),
            NamedFunctionCall(..) => {
                self.interp_named_func_call(arena, ctx, stack, next, parse_idx)
            }

            Delete(_) => todo!(),
            UnaryPlus(_) => todo!(),

            ConditionalOperator(_) => todo!(),

            This(_) => todo!(),
            List(_, _) => self.interp_list(ctx, stack, next, parse_idx),
            Parameter(_, _, _) => Ok(()),
            Null(loc) => ctx.push_expr(ExprRet::Null, self).into_expr_err(loc),
            YulExpr(FlatYulExpr::YulStartBlock) => {
                self.increment_asm_block();
                Ok(())
            }
            YulExpr(yul @ FlatYulExpr::YulVariable(..)) => self.interp_yul_var(arena, ctx, yul),
            YulExpr(yul @ FlatYulExpr::YulFuncCall(..)) => {
                self.interp_yul_func_call(arena, ctx, stack, yul)
            }
            YulExpr(FlatYulExpr::YulSuffixAccess(..)) => Ok(()),
            YulExpr(yul @ FlatYulExpr::YulAssign(..)) => self.interp_yul_assign(arena, ctx, yul),
            YulExpr(yul @ FlatYulExpr::YulFuncDef(..)) => {
                self.interp_yul_func_def(arena, ctx, stack, yul, parse_idx)
            }
            YulExpr(yul @ FlatYulExpr::YulVarDecl(..)) => {
                self.interp_yul_var_decl(arena, ctx, stack, yul, parse_idx)
            }
            YulExpr(FlatYulExpr::YulEndBlock) => {
                self.decrement_asm_block();
                Ok(())
            }
        }?;

        if matches!(self.peek_expr_flag(), Some(ExprFlag::Requirement))
            && !matches!(next, Requirement(..))
        {
            let _ = self.take_expr_flag();
            let loc = next.try_loc().unwrap();
            let mut lhs = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            let lhs = lhs.swap_remove(0);
            let cnode = ConcreteNode::from(self.add_node(Concrete::Bool(true)));
            let tmp_true = ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                .into_expr_err(loc)?;
            let rhs = ExprRet::Single(self.add_node(tmp_true));
            self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Eq, loc)
        } else {
            Ok(())
        }
    }

    fn interp_bit_not(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::BitwiseNot(loc) = next else {
            unreachable!()
        };

        let to_not = ctx
            .pop_n_latest_exprs(1, loc, self)
            .into_expr_err(loc)?
            .swap_remove(0);

        self.bit_not_inner(arena, ctx, to_not, loc)
    }

    fn interp_list(
        &mut self,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
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

        let mut new_values = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
        new_values.reverse();
        ctx.push_expr(ExprRet::Multi(new_values), self)
            .into_expr_err(loc)?;
        Ok(())
    }

    fn interp_member_access(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::MemberAccess(loc, name) = next else {
            unreachable!()
        };

        let member = ctx
            .pop_n_latest_exprs(1, loc, self)
            .into_expr_err(loc)?
            .swap_remove(0);
        self.member_access(arena, ctx, member, name, loc)
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
        stack: &mut Vec<FlatExpr>,
        if_expr: FlatExpr,
        parse_idx: usize,
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

        let (true_subctx, false_subctx) =
            Context::add_fork_subctxs(self, ctx, loc).into_expr_err(loc)?;

        // Parse the true condition expressions then skip the
        // false condition expressions, thus resulting in the
        // true_subctx parse_idx being the start of true body
        for _ in 0..true_cond {
            self.interpret_step(arena, true_subctx, loc, stack)?;
        }
        self.modify_edges(true_subctx, loc, &|analyzer, true_subctx| {
            true_subctx.skip_n_exprs(false_cond, analyzer);
            Ok(())
        })?;

        // Skip the true condition expressions then parse the false
        // condition expressions
        false_subctx.skip_n_exprs(true_cond, self);
        for _ in 0..false_cond {
            self.interpret_step(arena, false_subctx, loc, stack)?;
        }

        let true_killed = true_subctx.is_killed(self).into_expr_err(loc)?
            || true_subctx.unreachable(self, arena).into_expr_err(loc)?;
        let false_killed = false_subctx.is_killed(self).into_expr_err(loc)?
            || false_subctx.unreachable(self, arena).into_expr_err(loc)?;

        match (true_killed, false_killed) {
            (true, true) => {
                // both have been killed, delete the child and dont process the bodies
                ctx.delete_child(self).into_expr_err(loc)?;
            }
            (true, false) => {
                // the true context has been killed, delete child, process the false fork expression
                // in the parent context and parse the false body
                ctx.delete_child(self).into_expr_err(loc)?;

                // point the parse index of the parent ctx to the false body
                ctx.underlying_mut(self).unwrap().parse_idx =
                    parse_idx + true_cond + false_cond + true_body;
                for _ in 0..false_body {
                    self.interpret_step(arena, ctx, loc, stack)?;
                }
            }
            (false, true) => {
                // the false context has been killed, delete child, process the true fork expression
                // in the parent context and parse the true body
                ctx.delete_child(self).into_expr_err(loc)?;

                // point the parse index of the parent ctx to the true body
                ctx.underlying_mut(self).unwrap().parse_idx = parse_idx + true_cond + false_cond;
                for _ in 0..true_body {
                    self.interpret_step(arena, ctx, loc, stack)?;
                }
            }
            (false, false) => {
                // both branches are reachable. process each body
                for _ in 0..true_body {
                    self.interpret_step(arena, true_subctx, loc, stack)?;
                }
                // skip the false body expressions
                self.modify_edges(true_subctx, loc, &|analyzer, true_subctx| {
                    true_subctx.skip_n_exprs(false_body, analyzer);
                    Ok(())
                })?;

                // skip the true body expressions
                self.modify_edges(false_subctx, loc, &|analyzer, false_subctx| {
                    false_subctx.skip_n_exprs(true_body, analyzer);
                    Ok(())
                })?;
                // parse the false body expressions
                for i in 0..false_body {
                    self.interpret_step(arena, false_subctx, loc, stack)?;
                }
            }
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

        if matches!(self.peek_expr_flag(), Some(ExprFlag::Requirement)) {
            self.take_expr_flag();
            match cmp {
                FlatExpr::Equal(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Eq, loc)
                }
                FlatExpr::NotEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Neq, loc)
                }
                FlatExpr::Less(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Lt, loc)
                }
                FlatExpr::More(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Gt, loc)
                }
                FlatExpr::LessEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Lte, loc)
                }
                FlatExpr::MoreEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Gte, loc)
                }
                FlatExpr::Or(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Or, loc)
                }
                FlatExpr::And(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::And, loc)
                }
                _ => unreachable!(),
            }
        } else {
            match cmp {
                FlatExpr::Equal(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Eq, &rhs),
                FlatExpr::NotEqual(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Neq, &rhs),
                FlatExpr::Less(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Lt, &rhs),
                FlatExpr::More(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Gt, &rhs),
                FlatExpr::LessEqual(..) => {
                    self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Lte, &rhs)
                }
                FlatExpr::MoreEqual(..) => {
                    self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Gte, &rhs)
                }
                FlatExpr::LessEqual(..) => {
                    self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::And, &rhs)
                }
                FlatExpr::MoreEqual(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Or, &rhs),
                _ => unreachable!(),
            }
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
        stack: &mut Vec<FlatExpr>,
        var: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Variable(loc, name) = var else {
            unreachable!()
        };

        match self.take_expr_flag() {
            Some(ExprFlag::FunctionName(n, super_call, named_args)) => {
                let maybe_names = if named_args {
                    let start = parse_idx + 1;
                    Some(self.get_named_args(stack, start, n))
                } else {
                    None
                };
                let maybe_fn = if super_call {
                    self.find_super_func(arena, ctx, name.to_string(), n, maybe_names)
                        .into_expr_err(loc)?
                } else {
                    self.find_func(arena, ctx, name.to_string(), n, maybe_names)
                        .into_expr_err(loc)?
                };

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

    fn interp_array_idx(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        arr_idx: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::ArrayIndexAccess(loc) = arr_idx else {
            unreachable!()
        };
        let res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
        let [arr_ty, arr_idx] = into_sized(res);

        self.index_into_array_inner(arena, ctx, arr_ty.flatten(), arr_idx.flatten(), loc)
    }

    fn interp_named_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        func_call: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::NamedFunctionCall(loc, n) = func_call else {
            unreachable!()
        };

        let names_start = parse_idx.saturating_sub(n);
        let names = self.get_named_args(stack, names_start, n);

        self.interp_func_call(arena, ctx, func_call, Some(names))
    }

    fn get_named_args(
        &self,
        stack: &mut Vec<FlatExpr>,
        start: usize,
        n: usize,
    ) -> Vec<&'static str> {
        stack[start..start + n]
            .iter()
            .map(|named_arg| {
                let FlatExpr::NamedArgument(_, name) = named_arg else {
                    unreachable!()
                };
                *name
            })
            .collect::<Vec<_>>()
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

        // order the named inputs
        let inputs = if n > 0 {
            let res = if let Some(input_names) = input_names {
                let mut ret = Ok(None);
                let ordered_names = match self.node(func) {
                    Node::ContextVar(..) => match ContextVarNode::from(func).ty(self).unwrap() {
                        VarType::User(TypeNode::Func(func), _) => func.ordered_param_names(self),
                        VarType::User(TypeNode::Struct(strukt), _) => {
                            strukt.ordered_new_param_names(self)
                        }
                        VarType::User(TypeNode::Contract(con), _) => {
                            con.ordered_new_param_names(self)
                        }
                        other => todo!("Unhandled named arguments parent: {other:?}"),
                    },
                    Node::Function(..) => FunctionNode::from(func).ordered_param_names(self),
                    Node::Struct(..) => StructNode::from(func).ordered_new_param_names(self),
                    Node::Contract(..) => ContractNode::from(func).ordered_new_param_names(self),
                    other => todo!("Unhandled named arguments parent: {other:?}"),
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
            VarType::User(TypeNode::Contract(c), _) => {
                self.construct_contract_inner(arena, ctx, c, inputs, loc)
            }
            VarType::User(TypeNode::Func(s), _) => {
                if self.builtin_fn_nodes().iter().any(|(_, v)| *v == func) {
                    // its a builtin function call
                    self.call_builtin(arena, ctx, &s.name(self).into_expr_err(loc)?, inputs, loc)
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
            e => todo!("Unhandled ty: {e:?}"),
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

    fn interp_yul_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        next: FlatYulExpr,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulFuncCall(loc, name, num_inputs) = next else {
            unreachable!()
        };
        let inputs = ExprRet::Multi(
            ctx.pop_n_latest_exprs(num_inputs, loc, self)
                .into_expr_err(loc)?,
        );
        self.yul_func_call(
            arena,
            ctx,
            stack,
            name,
            inputs,
            self.current_asm_block(),
            loc,
        )
    }

    fn interp_yul_var(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatYulExpr,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulVariable(loc, name) = next else {
            unreachable!()
        };

        self.variable(
            arena,
            &solang_parser::pt::Identifier {
                loc,
                name: name.to_string(),
            },
            ctx,
            None,
            None,
        )?;

        if let Some(ret) = ctx.pop_expr_latest(loc, self).into_expr_err(loc)? {
            if ContextVarNode::from(ret.expect_single().into_expr_err(loc)?)
                .is_memory(self)
                .into_expr_err(loc)?
            {
                // its a memory based variable, push a uint instead
                let b = Builtin::Uint(256);
                let var = ContextVar::new_from_builtin(loc, self.builtin_or_add(b).into(), self)
                    .into_expr_err(loc)?;
                let node = self.add_node(var);
                ctx.push_expr(ExprRet::Single(node), self)
                    .into_expr_err(loc)
            } else {
                ctx.push_expr(ret, self).into_expr_err(loc)
            }
        } else {
            Err(ExprErr::Unresolved(
                loc,
                format!("Could not find yul variable with name: {name}"),
            ))
        }
    }

    fn interp_yul_func_def(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        next: FlatYulExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulFuncDef(loc, name, num) = next else {
            unreachable!()
        };

        let end = parse_idx + 1 + num;
        let exprs = (&stack[parse_idx + 1..end]).to_vec();
        let fn_node = ctx.associated_fn(self).into_expr_err(loc)?;
        let yul_fn = self.add_node(YulFunction::new(exprs, name, loc));
        self.add_edge(yul_fn, fn_node, Edge::YulFunction(self.current_asm_block()));
        ctx.underlying_mut(self).into_expr_err(loc)?.parse_idx = end;
        Ok(())
    }

    fn interp_yul_assign(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatYulExpr,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulAssign(loc, num) = next else {
            unreachable!()
        };

        let to_assign = ctx
            .pop_n_latest_exprs(num * 2, loc, self)
            .into_expr_err(loc)?;
        let (to_assign_to, assignments) = to_assign.split_at(to_assign.len() / 2);
        assert!(assignments.len() == to_assign_to.len());
        to_assign_to
            .iter()
            .zip(assignments)
            .try_for_each(|(lhs, rhs)| self.match_assign_sides(arena, ctx, loc, lhs, rhs))
    }

    fn interp_yul_var_decl(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        next: FlatYulExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulVarDecl(loc, num, assign) = next else {
            unreachable!()
        };

        if assign {
            let names = stack[parse_idx - num * 2..parse_idx]
                .iter()
                .filter_map(|s| match s {
                    FlatExpr::VarDef(_, Some(name), _, _) => Some(name),
                    _ => None,
                })
                .collect::<Vec<_>>();

            names.iter().try_for_each(|name| {
                self.variable(
                    arena,
                    &Identifier {
                        loc,
                        name: name.to_string(),
                    },
                    ctx,
                    None,
                    None,
                )
            })?;
            let to_assign = ctx
                .pop_n_latest_exprs(num * 2, loc, self)
                .into_expr_err(loc)?;
            let (to_assign_to, assignments) = to_assign.split_at(to_assign.len() / 2);
            assert!(assignments.len() == to_assign_to.len());
            to_assign_to
                .iter()
                .zip(assignments)
                .try_for_each(|(lhs, rhs)| self.match_assign_sides(arena, ctx, loc, lhs, rhs))
        } else {
            Ok(())
        }
    }

    fn modify_edges(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        closure: &impl Fn(&mut Self, ContextNode) -> Result<(), GraphError>,
    ) -> Result<(), ExprErr> {
        let live_edges = ctx.live_edges(self).into_expr_err(loc)?;
        if !ctx.killed_or_ret(self).into_expr_err(loc)? {
            if ctx.underlying(self).into_expr_err(loc)?.child.is_some() {
                if live_edges.is_empty() {
                    Ok(())
                } else {
                    live_edges
                        .iter()
                        .try_for_each(|ctx| closure(self, *ctx))
                        .into_expr_err(loc)
                }
            } else if live_edges.is_empty() {
                closure(self, ctx).into_expr_err(loc)
            } else {
                live_edges
                    .iter()
                    .try_for_each(|ctx| closure(self, *ctx))
                    .into_expr_err(loc)
            }
        } else {
            Ok(())
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
        stack: &mut Vec<FlatExpr>,
        closure: &impl Fn(
            &mut Self,
            &mut RangeArena<Elem<Concrete>>,
            ContextNode,
            Loc,
            &mut Vec<FlatExpr>,
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
