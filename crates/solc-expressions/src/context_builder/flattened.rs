use crate::{
    context_builder::{test_command_runner::TestCommandRunner, ContextBuilder},
    func_call::{
        func_caller::FuncCaller,
        internal_call::{FindFunc, InternalFuncCaller},
        intrinsic_call::*,
    },
    loops::Looper,
    yul::YulBuilder,
    yul::YulFuncCaller,
    ErrType, ExprTyParser, SolcError,
};
use graph::{
    elem::{Elem, RangeConcrete, RangeDyn, RangeExpr, RangeOp},
    nodes::{
        BuiltInNode, Builtin, CallFork, Concrete, ConcreteNode, Context, ContextNode, ContextVar,
        ContextVarNode, ContractId, ContractNode, EnvCtx, ExprRet, FunctionNode, KilledKind,
        StructNode, TmpConstruction, YulFunction,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, SolcRange, TypeNode, VarType,
};
use shared::{
    post_to_site, string_to_static, ElseOrDefault, ExprErr, ExprFlag, FlatExpr, FlatYulExpr,
    GraphError, IfElseChain, IntoExprErr, NodeIdx, RangeArena, USE_DEBUG_SITE,
};

use alloy_primitives::U256;
use solang_parser::pt::{
    CatchClause, CodeLocation, Expression, Identifier, Loc, Statement, YulExpression, YulStatement,
};

use std::collections::BTreeMap;

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
            Args(_, args) => {
                // statements are left to right
                args.iter().for_each(|arg| {
                    self.traverse_expression(&arg.expr, unchecked);
                });

                args.iter().for_each(|arg| {
                    self.push_expr(FlatExpr::from(arg));
                });
            }
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

                // do the false condition first, and take it off the stack, do the true condition, then add this back
                match cmp {
                    FlatExpr::And(loc, _, rhs_start, rhs_end) => {
                        let mut rhs = self
                            .expr_stack_mut()
                            .drain(rhs_start..rhs_end)
                            .collect::<Vec<_>>();
                        let rhs_cmp = rhs.pop().unwrap();
                        let lhs_cmp = self.expr_stack_mut().pop().unwrap();
                        if let Some(lhs_inv) = lhs_cmp.try_inv_cmp() {
                            self.push_expr(lhs_inv);
                        } else {
                            self.push_expr(lhs_cmp);
                            self.push_expr(FlatExpr::Not(loc));
                        }

                        self.expr_stack_mut().extend(rhs);
                        if let Some(rhs_inv) = rhs_cmp.try_inv_cmp() {
                            self.push_expr(rhs_inv);
                        } else {
                            self.push_expr(rhs_cmp);
                            self.push_expr(FlatExpr::Not(loc));
                        }

                        self.push_expr(FlatExpr::CmpRequirement(loc, false, false));
                        self.push_expr(FlatExpr::Or(loc));
                    }
                    _ => {
                        if let Some(inv) = cmp.try_inv_cmp() {
                            self.push_expr(FlatExpr::CmpRequirement(*loc, false, false));
                            self.push_expr(inv)
                        } else {
                            self.push_expr(cmp);
                            self.push_expr(FlatExpr::Not(*loc));
                            self.push_expr(FlatExpr::Requirement(*loc, false, false));
                        }
                    }
                }

                let false_cond = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                self.traverse_expression(if_expr, unchecked);
                let cmp = self.expr_stack_mut().pop().unwrap();
                self.traverse_requirement(cmp, if_expr.loc(), false, false);
                let true_cond = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
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
            While(loc, if_expr, body) => {
                let start_len = self.expr_stack_mut().len();
                self.traverse_expression(if_expr, unchecked);
                let cmp = self.expr_stack_mut().pop().unwrap();
                self.traverse_requirement(cmp, if_expr.loc(), false, false);
                let cond_exprs = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                let condition = cond_exprs.len();

                self.traverse_statement(body, unchecked);
                let body_exprs = self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>();
                let body = body_exprs.len();

                self.push_expr(FlatExpr::While {
                    loc: *loc,
                    condition,
                    body,
                });
                let stack = self.expr_stack_mut();
                stack.extend(cond_exprs);
                stack.extend(body_exprs);
            }
            For(loc, maybe_for_start, maybe_for_cond, maybe_for_after_each, maybe_for_body) => {
                let start_len = self.expr_stack_mut().len();

                let for_start_exprs = if let Some(start) = maybe_for_start {
                    self.traverse_statement(start, unchecked);
                    self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>()
                } else {
                    vec![]
                };
                let start = for_start_exprs.len();

                let for_cond_exprs = if let Some(cond) = maybe_for_cond {
                    self.traverse_expression(cond, unchecked);
                    let cmp = self.expr_stack_mut().pop().unwrap();
                    self.traverse_requirement(cmp, cond.loc(), false, false);
                    self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>()
                } else {
                    vec![]
                };
                let condition = for_cond_exprs.len();

                let for_body_exprs = if let Some(body) = maybe_for_body {
                    self.traverse_statement(body, unchecked);
                    self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>()
                } else {
                    vec![]
                };
                let body = for_body_exprs.len();

                let for_after_each_exprs = if let Some(after_each) = maybe_for_after_each {
                    self.traverse_expression(after_each, unchecked);
                    self.expr_stack_mut().drain(start_len..).collect::<Vec<_>>()
                } else {
                    vec![]
                };
                let after_each = for_after_each_exprs.len();

                self.push_expr(FlatExpr::For {
                    loc: *loc,
                    start,
                    condition,
                    after_each,
                    body,
                });
                let stack = self.expr_stack_mut();
                stack.extend(for_start_exprs);
                stack.extend(for_cond_exprs);
                stack.extend(for_body_exprs);
                stack.extend(for_after_each_exprs);
            }
            DoWhile(loc, _while_stmt, _while_expr) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "Do While statements are currently unsupported",
                ));
            }
            Expression(_, expr) => {
                match expr {
                    solang_parser::pt::Expression::StringLiteral(lits) if lits.len() == 1 => {
                        if lits[0].string.starts_with("pyro::") {
                            self.push_expr(FlatExpr::TestCommand(
                                lits[0].loc,
                                string_to_static(lits[0].string.clone()),
                            ));
                            return;
                        }
                    }
                    _ => {}
                }
                self.traverse_expression(expr, unchecked);
            }
            Continue(loc) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "continue statements are currently unsupported",
                ));
                // self.push_expr(FlatExpr::Continue(*loc));
            }
            Break(loc) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "break statements are currently unsupported",
                ));
                // self.push_expr(FlatExpr::Break(*loc));
            }
            Assembly {
                loc: _,
                dialect: _,
                flags: _,
                block: yul_block,
            } => {
                self.increment_asm_block();
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulStartBlock(
                    self.current_asm_block(),
                )));
                self.traverse_yul_statement(&YulStatement::Block(yul_block.clone()));
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulEndBlock(
                    self.current_asm_block(),
                )));
            }
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    self.traverse_expression(ret_expr, unchecked);
                }

                self.push_expr(FlatExpr::Return(*loc, maybe_ret_expr.is_some()));
            }
            Revert(loc, maybe_err_path, exprs) => {
                // println!(
                //     "err path? {maybe_err_path:?}, {:#?}",
                //     exprs.iter().map(|i| i.to_string()).collect::<Vec<_>>()
                // );
                exprs.iter().rev().for_each(|expr| {
                    self.traverse_expression(expr, unchecked);
                });

                if let Some(err_path) = maybe_err_path {
                    if err_path.identifiers.len() != 1 {
                        todo!("Multiple identifiers in identifier path?")
                    }
                    let err_name = err_path.identifiers[0].clone();
                    self.push_expr(FlatExpr::FunctionCallName {
                        num_inputs: exprs.len(),
                        call_block_inputs: 0,
                        is_super: false,
                        named_args: false,
                    });
                    self.traverse_expression(
                        &solang_parser::pt::Expression::Variable(err_name.clone()),
                        unchecked,
                    );
                    self.push_expr(FlatExpr::FunctionCall {
                        loc: err_name.loc,
                        maybe_target: None,
                        num_inputs: exprs.len(),
                        num_call_block_inputs: 0,
                    })
                }
                self.push_expr(FlatExpr::Revert(
                    *loc,
                    maybe_err_path.is_some(),
                    exprs.len(),
                ))
            }
            RevertNamedArgs(loc, maybe_err_path, named_args) => {
                named_args.iter().rev().for_each(|arg| {
                    self.traverse_expression(&arg.expr, unchecked);
                });
                if let Some(err_path) = maybe_err_path {
                    if err_path.identifiers.len() != 1 {
                        todo!("Multiple identifiers in identifier path?")
                    }
                    let err_name = err_path.identifiers[0].clone();
                    self.push_expr(FlatExpr::FunctionCallName {
                        num_inputs: named_args.len(),
                        call_block_inputs: 0,
                        is_super: false,
                        named_args: true,
                    });
                    self.traverse_expression(
                        &solang_parser::pt::Expression::Variable(err_name.clone()),
                        unchecked,
                    );
                    named_args.iter().for_each(|arg| {
                        self.push_expr(FlatExpr::from(arg));
                    });
                    self.push_expr(FlatExpr::FunctionCall {
                        loc: err_name.loc,
                        maybe_target: None,
                        num_inputs: named_args.len(),
                        num_call_block_inputs: 0,
                    })
                }
                self.push_expr(FlatExpr::Revert(
                    *loc,
                    maybe_err_path.is_some(),
                    named_args.len(),
                ));
            }
            Emit(_loc, _emit_expr) => {
                // self.traverse_expression(emit_expr, unchecked);
                // self.push_expr(FlatExpr::Emit(*loc));
            }
            Try(loc, try_expr, maybe_returns, clauses) => {
                if maybe_returns.is_none() {
                    self.push_expr(FlatExpr::Todo(
                        *loc,
                        "Try-Catch without returns are currently not supported",
                    ));
                    return;
                }
                self.push_expr(FlatExpr::Try(*loc));
                self.traverse_expression(try_expr, unchecked);
                // There can be only one `Simple` catch clause
                // it will always be checked last after more specific ones
                // fall through
                let mut c = clauses.clone();
                c.sort_by(|a, b| match (a, b) {
                    (CatchClause::Named(..), CatchClause::Named(..)) => std::cmp::Ordering::Equal,
                    (CatchClause::Simple(..), CatchClause::Named(..)) => {
                        std::cmp::Ordering::Greater
                    }
                    (CatchClause::Named(..), CatchClause::Simple(..)) => std::cmp::Ordering::Less,
                    _ => {
                        self.push_expr(FlatExpr::InvalidSolidity(
                            *loc,
                            "Invalid solidity - you cannot have more than 1 catch-all clauses",
                        ));
                        std::cmp::Ordering::Equal
                    }
                });

                // i.e.: try .. {} catch MyError(..) { block0 } catch MyOtherError(..) { block1 } catch { block2 }
                // converts into:
                // if (failed) {
                //  if type(error) == MyError {
                //      block0;
                //  } else if type(error) == MyOtherError{
                //      block1;
                //  } else {
                //      block2;
                //  }
                // } else {
                //   maybe_returns
                // }
                #[derive(Default, Debug)]
                struct IfChain {
                    pub loc: Loc,
                    pub true_cond: Vec<FlatExpr>,
                    pub false_cond: Vec<FlatExpr>,
                    pub true_body: Vec<FlatExpr>,
                    pub false_body: Vec<FlatExpr>,
                }

                impl IfChain {
                    fn iffer(&self) -> FlatExpr {
                        FlatExpr::If {
                            loc: self.loc,
                            true_cond: self.true_cond.len(),
                            false_cond: self.false_cond.len(),
                            true_body: self.true_body.len(),
                            false_body: self.false_body.len(),
                        }
                    }

                    fn flatten(self) -> Vec<FlatExpr> {
                        let iffer = self.iffer();
                        let mut flattened = vec![iffer];
                        flattened.extend(self.true_cond);
                        flattened.extend(self.false_cond);
                        flattened.extend(self.true_body);
                        flattened.extend(self.false_body);
                        flattened
                    }
                    fn join_false_body(&mut self, child_false_body: Self) {
                        self.false_body.extend(child_false_body.flatten());
                    }
                }

                let mut prev_if = None;
                let mut catch_all = None;
                for clause in c.iter().rev() {
                    let mut if_chain = IfChain::default();
                    match clause {
                        CatchClause::Named(loc, name, param, block) => {
                            if_chain.loc = *loc;
                            // get error type
                            let true_cond_start = self.expr_stack().len();
                            let mut true_body_prefix = vec![];
                            match &*name.name {
                                "Error" => {
                                    self.push_expr(FlatExpr::Dup);
                                    self.push_expr(FlatExpr::TryErrCheck(*loc, "Error"));
                                    let len = self.expr_stack().len();
                                    self.push_expr(FlatExpr::MemberAccess(param.loc, "reason"));
                                    let list = solang_parser::pt::Expression::List(
                                        param.loc,
                                        vec![(param.loc, Some(param.clone()))],
                                    );
                                    self.traverse_expression(&list, unchecked);
                                    self.push_expr(FlatExpr::Swap);
                                    self.push_expr(FlatExpr::Assign(param.loc));
                                    true_body_prefix =
                                        self.expr_stack_mut().drain(len..).collect::<Vec<_>>();
                                }
                                "Panic" => {
                                    self.push_expr(FlatExpr::Dup);
                                    self.push_expr(FlatExpr::TryErrCheck(*loc, "Panic"));
                                }
                                _ => {
                                    self.push_expr(FlatExpr::InvalidSolidity(
                                        *loc,
                                        "Only Error(..) or Panic(..) are allowed in catch clauses",
                                    ));
                                    break;
                                }
                            }

                            let mut true_cond = self
                                .expr_stack_mut()
                                .drain(true_cond_start..)
                                .collect::<Vec<_>>();
                            let mut false_cond = true_cond.clone();
                            true_cond.push(FlatExpr::Requirement(*loc, false, false));
                            false_cond.push(FlatExpr::Not(*loc));
                            false_cond.push(FlatExpr::Requirement(*loc, false, false));
                            self.traverse_statement(block, unchecked);
                            let mut true_body = true_body_prefix;
                            true_body.extend(
                                self.expr_stack_mut()
                                    .drain(true_cond_start..)
                                    .collect::<Vec<_>>(),
                            );

                            if_chain.true_cond = true_cond;
                            if_chain.false_cond = false_cond;
                            if_chain.true_body = true_body;

                            if let Some(prev) = prev_if {
                                if_chain.join_false_body(prev);
                            } else if let Some(catch_all) = catch_all.take() {
                                if_chain.false_body = catch_all;
                            } else {
                                // no more catches, revert
                                if_chain.false_body = vec![FlatExpr::Revert(*loc, false, 0)];
                            };
                            prev_if = Some(if_chain);
                        }
                        CatchClause::Simple(loc, maybe_bytes, block) => {
                            if_chain.loc = *loc;
                            let catch_all_body = self.expr_stack().len();
                            self.traverse_statement(block, unchecked);
                            catch_all = Some(
                                self.expr_stack_mut()
                                    .drain(catch_all_body..)
                                    .collect::<Vec<_>>(),
                            );
                        }
                    }
                }

                let mut true_body = vec![];
                if let Some(rets) = maybe_returns {
                    let true_body_start = self.expr_stack().len();
                    let list = solang_parser::pt::Expression::List(*loc, rets.0.clone());
                    self.traverse_expression(&list, unchecked);
                    self.traverse_statement(&rets.1, unchecked);
                    true_body = self
                        .expr_stack_mut()
                        .drain(true_body_start..)
                        .collect::<Vec<_>>();
                }

                match (prev_if, catch_all) {
                    (Some(prev_if), None) => {
                        let true_cond = vec![
                            FlatExpr::CallSuccess(*loc),
                            FlatExpr::Requirement(*loc, false, false),
                        ];
                        let false_cond = vec![
                            FlatExpr::CallSuccess(*loc),
                            FlatExpr::Not(*loc),
                            FlatExpr::Requirement(*loc, false, false),
                        ];
                        let flattened_catches = prev_if.flatten();
                        let entry_if = FlatExpr::If {
                            loc: *loc,
                            true_cond: 2,
                            false_cond: 3,
                            true_body: true_body.len(),
                            false_body: flattened_catches.len(),
                        };
                        self.push_expr(entry_if);
                        self.expr_stack_mut().extend(true_cond);
                        self.expr_stack_mut().extend(false_cond);
                        self.expr_stack_mut().extend(true_body);
                        self.expr_stack_mut().extend(flattened_catches);
                    }
                    (None, Some(catch_all)) => {
                        let true_cond = vec![
                            FlatExpr::CallSuccess(*loc),
                            FlatExpr::Requirement(*loc, false, false),
                        ];
                        let false_cond = vec![
                            FlatExpr::CallSuccess(*loc),
                            FlatExpr::Not(*loc),
                            FlatExpr::Requirement(*loc, false, false),
                        ];
                        let entry_if = FlatExpr::If {
                            loc: *loc,
                            true_cond: 2,
                            false_cond: 3,
                            true_body: true_body.len(),
                            false_body: catch_all.len(),
                        };
                        self.push_expr(entry_if);
                        self.expr_stack_mut().extend(true_cond);
                        self.expr_stack_mut().extend(false_cond);
                        self.expr_stack_mut().extend(true_body);
                        self.expr_stack_mut().extend(catch_all);
                    }
                    _ => self.push_expr(FlatExpr::InvalidSolidity(*loc, "Misconfigured try-catch")),
                }
            }
            Error(_loc) => {}
        }
    }

    fn traverse_requirement(&mut self, cmp: FlatExpr, loc: Loc, with_str: bool, assertion: bool) {
        match cmp {
            FlatExpr::And(_, lhs_start, rhs_start, rhs_end) => {
                // Its better to just break up And into its component
                // parts now as opposed to trying to do it later
                // i.e.:
                // require(x && y) ==>
                //   require(x);
                //   require(y);

                let mut rhs = self
                    .expr_stack_mut()
                    .drain(rhs_start..rhs_end)
                    .collect::<Vec<_>>();
                let rhs_cmp = rhs.pop().unwrap();
                let mut lhs = self
                    .expr_stack_mut()
                    .drain(lhs_start..rhs_start)
                    .collect::<Vec<_>>();
                let lhs_cmp = lhs.pop().unwrap();

                if with_str {
                    self.push_expr(FlatExpr::Dup);
                }
                self.expr_stack_mut().extend(lhs);
                // We have to reset the stack to before the edits because
                // `And`s use absolute positioning, so if we change out the stack it gets a bit screwed up.
                // So we edit the rhs cmp, then replace it with the original
                let len = self.expr_stack().len();
                self.traverse_requirement(lhs_cmp, loc, with_str, assertion);
                let new_lhs = self.expr_stack_mut().drain(len..).collect::<Vec<_>>();
                let len = self.expr_stack().len();
                self.expr_stack_mut().extend(rhs);
                self.traverse_requirement(rhs_cmp, loc, with_str, assertion);
                let new_rhs = self.expr_stack_mut().drain(len..).collect::<Vec<_>>();
                self.expr_stack_mut().extend(new_lhs);
                self.expr_stack_mut().extend(new_rhs);
            }
            FlatExpr::Less(_)
            | FlatExpr::More(_)
            | FlatExpr::LessEqual(_)
            | FlatExpr::MoreEqual(_)
            | FlatExpr::Equal(_)
            | FlatExpr::NotEqual(_)
            | FlatExpr::Or(_) => {
                self.push_expr(FlatExpr::CmpRequirement(loc, with_str, assertion));
                self.push_expr(cmp);
            }
            _ => {
                self.push_expr(cmp);
                self.push_expr(FlatExpr::Requirement(loc, with_str, assertion));
            }
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
            For(yul_for) => {
                self.push_expr(FlatExpr::Todo(
                    yul_for.loc,
                    "Yul for statements are currently unsupported",
                ));
            }
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
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "yul 'leave' statements are currently unsupported",
                ));
                // self.push_expr(FlatExpr::Break(*loc));
            }
            Break(loc) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "yul 'break' statements are currently unsupported",
                ));
                // self.push_expr(FlatExpr::Break(*loc));
            }
            Continue(loc) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "yul 'continue' statements are currently unsupported",
                ));
                // self.push_expr(FlatExpr::Continue(*loc));
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

                self.increment_asm_block();
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulStartBlock(
                    self.current_asm_block(),
                )));
                for stmt in def.body.statements.iter() {
                    self.traverse_yul_statement(stmt);
                }
                self.push_expr(FlatExpr::YulExpr(FlatYulExpr::YulEndBlock(
                    self.current_asm_block(),
                )));

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
            Error(loc) => {
                self.push_expr(FlatExpr::Todo(
                    *loc,
                    "yul 'error' statements are currently unsupported",
                ));
            }
        }
    }

    fn traverse_yul_if_else(&mut self, loc: Loc, iec: IfElseChain) {
        let true_body = &iec.true_stmt;
        let start_len = self.expr_stack_mut().len();
        self.push_expr(FlatExpr::NumberLiteral(loc, "0", "", None));
        self.traverse_yul_expression(&iec.if_expr);

        // have it be a require statement
        self.push_expr(FlatExpr::CmpRequirement(loc, false, false));
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
                self.traverse_expression(expr, unchecked);
                let func_call = self.expr_stack_mut().pop().unwrap();
                self.push_expr(FlatExpr::New(*new_loc));
                self.push_expr(func_call);
            }
            // Binary ops
            Power(loc, lhs, rhs) => {
                self.traverse_expression(rhs, unchecked);
                let rhs = self.expr_stack_mut().pop().unwrap();
                let zero_exp = match rhs {
                    FlatExpr::NumberLiteral(loc, int, exp, unit)
                        if int == "0" && unit.is_none() && exp.is_empty() =>
                    {
                        self.push_expr(FlatExpr::NumberLiteral(loc, "1", "", None));
                        true
                    }
                    FlatExpr::HexNumberLiteral(loc, int, _) => {
                        let all_zero = int
                            .strip_prefix("0x")
                            .unwrap_or(int)
                            .chars()
                            .all(|char| char == '0');
                        if all_zero {
                            self.push_expr(FlatExpr::NumberLiteral(loc, "1", "", None));
                            true
                        } else {
                            false
                        }
                    }
                    _ => false,
                };

                if !zero_exp {
                    self.push_expr(rhs);
                    self.traverse_expression(lhs, unchecked);
                    self.push_expr(FlatExpr::Power(*loc, unchecked.unwrap_or(false)));
                }
            }

            Add(_, lhs, rhs)
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

            Assign(_, lhs, rhs) => {
                self.traverse_expression(rhs, unchecked);
                self.traverse_expression(lhs, unchecked);
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
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
            | Equal(_, lhs, rhs)
            | NotEqual(_, lhs, rhs)
            | Less(_, lhs, rhs)
            | More(_, lhs, rhs)
            | LessEqual(_, lhs, rhs)
            | MoreEqual(_, lhs, rhs)
            | Or(_, lhs, rhs) => {
                self.traverse_expression(rhs, unchecked);
                self.traverse_expression(lhs, unchecked);
                self.push_expr(FlatExpr::try_from(parent_expr).unwrap());
            }

            And(loc, lhs, rhs) => {
                let lhs_start = self.expr_stack().len();
                self.traverse_expression(lhs, unchecked);
                let rhs_start = self.expr_stack().len();
                self.traverse_expression(rhs, unchecked);
                let rhs_end = self.expr_stack().len();
                self.push_expr(FlatExpr::And(*loc, lhs_start, rhs_start, rhs_end));
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
                self.push_expr(FlatExpr::ArrayTy(*loc, false));
            }
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                let start_len = self.expr_stack().len();
                self.traverse_expression(ty_expr, unchecked);
                let ty_exprs: Vec<_> = self.expr_stack_mut().drain(start_len..).collect();
                match ty_exprs.last().unwrap() {
                    FlatExpr::Type(..) | FlatExpr::ArrayTy(..) => {
                        // sized array defintion
                        self.traverse_expression(index_expr, unchecked);
                        self.expr_stack_mut().extend(ty_exprs);
                        self.push_expr(FlatExpr::ArrayTy(*loc, true));
                    }
                    _ => {
                        self.traverse_expression(index_expr, unchecked);
                        self.expr_stack_mut().extend(ty_exprs);
                        self.push_expr(FlatExpr::ArrayIndexAccess(*loc));
                    }
                }
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {
                // convert into statement if
                let as_stmt: Statement = Statement::If(
                    *loc,
                    *if_expr.clone(),
                    Box::new(Statement::Expression(true_expr.loc(), *true_expr.clone())),
                    Some(Box::new(Statement::Expression(
                        false_expr.loc(),
                        *false_expr.clone(),
                    ))),
                );
                self.traverse_statement(&as_stmt, unchecked);
            }
            ArraySlice(loc, lhs_expr, maybe_range_start, maybe_range_exclusive_end) => {
                let mut has_start = false;
                let mut has_end = false;
                if let Some(range_exclusive_end) = maybe_range_exclusive_end {
                    self.traverse_expression(range_exclusive_end, unchecked);
                    has_end = true;
                }

                if let Some(range_start) = maybe_range_start {
                    self.traverse_expression(range_start, unchecked);
                    has_start = true;
                }

                self.traverse_expression(lhs_expr, unchecked);

                self.push_expr(FlatExpr::ArraySlice(*loc, has_start, has_end));
            }
            ArrayLiteral(loc, val_exprs) => {
                val_exprs
                    .iter()
                    .rev()
                    .for_each(|val| self.traverse_expression(val, unchecked));
                self.push_expr(FlatExpr::ArrayLiteral(*loc, val_exprs.len()));
            }
            // Function calls
            FunctionCallBlock(loc, func_expr, call_block) => {
                match &**call_block {
                    Statement::Args(..) => {
                        // a.b{ <call args>}
                        self.traverse_expression(func_expr, unchecked);
                        let start_len = self.expr_stack().len();

                        self.traverse_statement(call_block, unchecked);
                        let mut call_args: Vec<FlatExpr> =
                            self.expr_stack_mut().drain(start_len..).collect();
                        let num_args = call_args
                            .iter()
                            .filter(|arg| matches!(arg, FlatExpr::NamedArgument(..)))
                            .count();
                        let fn_name = self.expr_stack_mut().pop().unwrap();
                        let call_names = call_args.split_off(num_args / 2);
                        self.expr_stack_mut().extend(call_args);
                        self.expr_stack_mut().extend(call_names);
                        self.push_expr(fn_name);
                        self.push_expr(FlatExpr::FunctionCallBlock(*loc, num_args));
                    }
                    Statement::Block { .. } => {
                        self.traverse_expression(func_expr, unchecked);
                        self.traverse_statement(call_block, unchecked);
                    }
                    e => todo!("Unhandled statement type in function call block: {e}"),
                }
            }
            NamedFunctionCall(loc, func_expr, input_args) => {
                let mut call_block_n = 0;
                self.traverse_expression(func_expr, unchecked);
                let expr = self.expr_stack_mut().pop().unwrap();
                match expr {
                    FlatExpr::Super(loc, name) => {
                        input_args.iter().rev().for_each(|arg| {
                            self.traverse_expression(&arg.expr, unchecked);
                        });
                        self.push_expr(FlatExpr::FunctionCallName {
                            num_inputs: input_args.len(),
                            call_block_inputs: 0,
                            is_super: true,
                            named_args: true,
                        });
                        self.push_expr(FlatExpr::Variable(loc, name));
                    }
                    FlatExpr::FunctionCallBlock(_, n) => {
                        call_block_n = n;
                        let fn_name = self.expr_stack_mut().pop().unwrap();
                        self.push_expr(expr);
                        input_args.iter().rev().for_each(|arg| {
                            self.traverse_expression(&arg.expr, unchecked);
                        });
                        self.push_expr(FlatExpr::FunctionCallName {
                            num_inputs: input_args.len(),
                            call_block_inputs: n,
                            is_super: false,
                            named_args: true,
                        });
                        self.push_expr(fn_name);
                    }
                    other => {
                        input_args.iter().rev().for_each(|arg| {
                            self.traverse_expression(&arg.expr, unchecked);
                        });
                        self.push_expr(FlatExpr::FunctionCallName {
                            num_inputs: input_args.len(),
                            call_block_inputs: call_block_n,
                            is_super: false,
                            named_args: true,
                        });
                        self.push_expr(other);
                    }
                }

                input_args.iter().for_each(|arg| {
                    self.push_expr(FlatExpr::from(arg));
                });
                self.push_expr(FlatExpr::NamedFunctionCall {
                    loc: *loc,
                    maybe_target: None,
                    num_inputs: input_args.len(),
                    num_call_block_inputs: call_block_n,
                });
            }
            FunctionCall(loc, func_expr, input_exprs) => match &**func_expr {
                Variable(Identifier { name, .. }) if matches!(&**name, "require" | "assert") => {
                    input_exprs.iter().enumerate().rev().for_each(|(_, expr)| {
                        self.traverse_expression(expr, unchecked);
                    });
                    let cmp = self.expr_stack_mut().pop().unwrap();
                    let with_str = input_exprs.len() > 1;
                    let assertion = matches!(&**name, "assert");
                    self.traverse_requirement(cmp, *loc, with_str, assertion);
                }
                _ => {
                    // func(inputs)
                    self.traverse_expression(func_expr, unchecked);

                    // For clarity we make these variables
                    let mut is_super = false;
                    let named_args = false;
                    let mut call_block_n = 0;
                    let num_inputs = input_exprs.len();
                    let kind = self.expr_stack_mut().pop().unwrap();
                    match kind {
                        FlatExpr::Super(loc, name) => {
                            input_exprs.iter().rev().for_each(|expr| {
                                self.traverse_expression(expr, unchecked);
                            });
                            is_super = true;
                            self.push_expr(FlatExpr::FunctionCallName {
                                num_inputs,
                                call_block_inputs: 0,
                                is_super,
                                named_args,
                            });
                            self.push_expr(FlatExpr::Variable(loc, name));
                        }
                        FlatExpr::FunctionCallBlock(_, n) => {
                            call_block_n = n;
                            let fn_name = self.expr_stack_mut().pop().unwrap();
                            let len = self.expr_stack().len();
                            let call_block_names =
                                self.expr_stack_mut().drain(len - n..).collect::<Vec<_>>();
                            input_exprs.iter().rev().for_each(|expr| {
                                self.traverse_expression(expr, unchecked);
                            });
                            self.push_expr(FlatExpr::FunctionCallName {
                                num_inputs,
                                call_block_inputs: n,
                                is_super,
                                named_args,
                            });
                            self.push_expr(fn_name);
                            self.expr_stack_mut().extend(call_block_names);
                            self.push_expr(kind);
                        }
                        FlatExpr::ArrayTy(..) => {
                            let mut full_fn = vec![kind];
                            let mut prev = self.expr_stack_mut().pop().unwrap();
                            while !matches!(prev, FlatExpr::Type(..) | FlatExpr::Variable(..)) {
                                full_fn.push(prev);
                                prev = self.expr_stack_mut().pop().unwrap();
                            }
                            full_fn.push(prev);
                            full_fn.reverse();
                            input_exprs.iter().rev().for_each(|expr| {
                                self.traverse_expression(expr, unchecked);
                            });
                            self.expr_stack_mut().extend(full_fn);
                        }
                        other => {
                            input_exprs.iter().rev().for_each(|expr| {
                                self.traverse_expression(expr, unchecked);
                            });
                            self.push_expr(FlatExpr::FunctionCallName {
                                num_inputs,
                                call_block_inputs: 0,
                                is_super,
                                named_args,
                            });
                            self.push_expr(other);
                        }
                    }

                    self.push_expr(FlatExpr::FunctionCall {
                        loc: *loc,
                        maybe_target: None,
                        num_inputs,
                        num_call_block_inputs: call_block_n,
                    });
                }
            },
            // member
            MemberAccess(loc, member_expr, ident) => match &**member_expr {
                Variable(Identifier { name, .. }) if name == "super" => {
                    self.push_expr(FlatExpr::Super(*loc, string_to_static(ident)));
                }
                Variable(Identifier { name, .. }) if name == "abi" => {
                    self.push_expr(FlatExpr::Variable(
                        *loc,
                        string_to_static(format!("abi.{ident}")),
                    ));
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

    fn interpret_entry_func(&mut self, func: FunctionNode, arena: &mut RangeArena<Elem<Concrete>>) {
        let loc = func
            .body_loc(self)
            .unwrap()
            .unwrap_or_else(|| func.definition_loc(self).unwrap());
        let raw_ctx = Context::new(
            func,
            self.add_if_err(func.name(self).into_expr_err(loc)).unwrap(),
            loc,
            ContractId::Id(self.increment_contract_id()),
        );
        let ctx = ContextNode::from(self.add_node(Node::Context(raw_ctx)));
        self.add_edge(ctx, func, Edge::Context(ContextEdge::Context));

        let res = func.add_params_to_ctx(self, ctx).into_expr_err(loc);
        self.add_if_err(res);

        let msg = self.msg().underlying(self).unwrap().clone();
        let env = EnvCtx::from_msg(self, &msg, loc, ctx).into_expr_err(loc);
        let env = self.add_if_err(env);

        let res = self.func_call_inner(
            arena,
            true, // entry_call
            ctx,
            func,
            func.definition_loc(self).unwrap(),
            &[],
            &[],
            None,  // alt function name
            &None, // mod state
            env,
            None, // not ext
            false,
        );
        let _ = self.add_if_err(res);
    }

    fn interpret(
        &mut self,
        ctx: ContextNode,
        body_loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        let mut stack = std::mem::take(self.expr_stack_mut());
        tracing::trace!("stack: {stack:#?}");

        while (!ctx.is_ended(self).unwrap() || ctx.has_live_edge(self).unwrap())
            && ctx.parse_idx(self) < stack.len()
        {
            let res = self.interpret_step(arena, ctx, body_loc, &mut stack);
            if unsafe { USE_DEBUG_SITE } {
                post_to_site(&*self, arena);
            }
            self.add_if_err(res);
        }

        if ctx.parse_idx(self) >= stack.len() {
            let ended = self.end(arena, &mut stack, ctx);
            self.add_if_err(ended);
        }
    }

    fn end(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        stack: &mut Vec<FlatExpr>,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        let mut loc = None;
        let mut stack_rev_iter = stack.iter().rev();
        let mut loccer = stack_rev_iter.next();
        while loc.is_none() && loccer.is_some() {
            loc = loccer.unwrap().try_loc();
            loccer = stack_rev_iter.next();
        }
        let loc = loc.unwrap_or(ctx.underlying(self).unwrap().loc);
        let fun = ctx.associated_fn(self).into_expr_err(loc)?;
        let vars = if ctx.return_nodes(self).unwrap().is_empty() {
            ExprRet::Multi(
                fun.returns(arena, self)
                    .iter()
                    .map(|ret| {
                        if let Some(name) = ret.maybe_name(self).ok()? {
                            ctx.return_var_by_name_or_recurse(self, &name)
                                .ok()
                                .flatten()
                        } else {
                            None
                        }
                    })
                    .map(|i| {
                        if let Some(var) = i {
                            ExprRet::Single(var.0.into())
                        } else {
                            ExprRet::Null
                        }
                    })
                    .collect::<Vec<_>>(),
            )
        } else {
            ExprRet::Multi(vec![])
        };

        if vars.nonnull_len() != 0 {
            self.return_match(arena, ctx, loc, vars, 0);
        } else {
            self.return_match(arena, ctx, loc, ExprRet::CtxKilled(KilledKind::Ended), 0);
        }

        Ok(())
    }

    fn interpret_step(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        body_loc: Loc,
        stack: &mut Vec<FlatExpr>,
    ) -> Result<(), ExprErr> {
        let res = self.flat_apply_to_edges(
            ctx,
            body_loc,
            arena,
            stack,
            &|analyzer: &mut Self,
              arena: &mut RangeArena<Elem<Concrete>>,
              ctx: ContextNode,
              _: Loc,
              stack: &mut Vec<FlatExpr>| {
                let res = analyzer.interpret_expr(arena, ctx, stack);
                if let Err(e) = res {
                    ctx.kill(analyzer, e.loc(), KilledKind::ParseError).unwrap();
                    Err(e)
                } else {
                    Ok(())
                }
            },
        );

        if let Err(e) = res {
            ctx.kill(self, e.loc(), KilledKind::ParseError).unwrap();
            Err(e)
        } else {
            Ok(())
        }
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
        tracing::trace!(
            "incrementing parse index: {}, {}",
            ctx.path(self),
            parse_idx
        );
        let Some(next) = stack.get(parse_idx) else {
            return self.end(arena, stack, ctx);
        };
        let next = *next;

        tracing::trace!(
            "parsing (idx: {parse_idx}) {:?} in context {} - flag: {:?}",
            next,
            ctx.path(self),
            ctx.peek_expr_flag(self)
        );

        if self.debug_stack() {
            tracing::trace!(
                "return stack: {}",
                ctx.debug_expr_stack_str_ranged(self, arena).unwrap()
            );
        }

        match next {
            Todo(loc, err_str) => Err(ExprErr::Todo(loc, err_str.to_string())),
            // Flag expressions
            FunctionCallName {
                num_inputs,
                call_block_inputs,
                is_super,
                named_args,
            } => {
                let try_catch = matches!(ctx.peek_expr_flag(self), Some(ExprFlag::Try));
                ctx.set_expr_flag(
                    self,
                    ExprFlag::FunctionName {
                        num_inputs,
                        call_block_inputs,
                        is_super,
                        named_args,
                        try_catch,
                    },
                );
                Ok(())
            }
            Negate(_) => {
                let try_catch = matches!(ctx.peek_expr_flag(self), Some(ExprFlag::Try));
                ctx.set_expr_flag(self, ExprFlag::Negate(try_catch));
                Ok(())
            }
            New(_) => {
                let try_catch = matches!(ctx.peek_expr_flag(self), Some(ExprFlag::Try));
                ctx.set_expr_flag(self, ExprFlag::New(try_catch));
                Ok(())
            }
            Try { .. } => {
                ctx.set_expr_flag(self, ExprFlag::Try);
                Ok(())
            }
            TryErrCheck(loc, name) => {
                let mut res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                let res = res.remove(0).expect_single().into_expr_err(loc)?;
                if let Some(err_node) = ContextVarNode::from(res)
                    .maybe_err_node(self)
                    .into_expr_err(loc)?
                {
                    let errors_match = err_node.name(self).into_expr_err(loc)? == name;
                    let errors_match_var =
                        self.add_concrete_var(ctx, Concrete::from(errors_match), loc)?;
                    ctx.push_expr(ExprRet::Single(errors_match_var.0.into()), self)
                        .into_expr_err(loc)
                } else {
                    let errors_match_var =
                        self.add_concrete_var(ctx, Concrete::from(false), loc)?;
                    ctx.push_expr(ExprRet::Single(errors_match_var.0.into()), self)
                        .into_expr_err(loc)
                }
            }
            CallSuccess(loc) => {
                let mut res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                let res = res.remove(0);
                ctx.push_expr(res.clone(), self).into_expr_err(loc)?;
                let call_res = res.flatten();
                match call_res {
                    ExprRet::Single(i) => {
                        let is_err = ContextVarNode::from(i).is_err(self).into_expr_err(loc)?;
                        let success_var =
                            self.add_concrete_var(ctx, Concrete::from(!is_err), loc)?;
                        ctx.push_expr(ExprRet::Single(success_var.0.into()), self)
                            .into_expr_err(loc)?;
                    }
                    _ => {
                        let success_var = self.add_concrete_var(ctx, Concrete::from(true), loc)?;
                        ctx.push_expr(ExprRet::Single(success_var.0.into()), self)
                            .into_expr_err(loc)?;
                    }
                }
                Ok(())
            }

            InvalidSolidity(loc, s) => Err(ExprErr::ParseError(loc, s.to_string())),

            // Literals
            AddressLiteral(loc, lit) => self.address_literal(ctx, loc, lit),
            StringLiteral(loc, lit) => self.string_literal(ctx, loc, lit),
            BoolLiteral(loc, b) => self.bool_literal(ctx, loc, b),
            HexLiteral(loc, hex) => self.hex_literals(ctx, loc, hex),
            NumberLiteral(..) | HexNumberLiteral(..) | RationalNumberLiteral(..) => {
                self.interp_negatable_literal(arena, ctx, next)
            }

            // Variable
            VarDef(..) => self.interp_var_def(arena, ctx, next),
            Type(..) => self.interp_type(arena, ctx, next),
            Variable(..) => self.interp_var(arena, ctx, stack, next, parse_idx),
            Assign(..) => self.interp_assign(arena, ctx, next),
            List(_, _) => self.interp_list(ctx, stack, next, parse_idx),
            This(_) => self.interp_this(ctx, next),
            Delete(_) => self.interp_delete(arena, ctx, next),

            // Conditional
            If { .. } => self.interp_if(arena, ctx, stack, next),
            CmpRequirement(_loc, with_str, assertion) => {
                let try_catch = matches!(ctx.peek_expr_flag(self), Some(ExprFlag::Try));
                ctx.set_expr_flag(self, ExprFlag::Requirement(try_catch, with_str, assertion));
                Ok(())
            }
            Requirement(loc, with_str, assertion) => {
                let _ = ctx.take_expr_flag(self);
                let pop_num = 1 + if with_str { 1 } else { 0 };
                let mut lhs = ctx
                    .pop_n_latest_exprs(pop_num, loc, self)
                    .into_expr_err(loc)?;
                let req = lhs.swap_remove(0);

                let err = if with_str {
                    let err = lhs.swap_remove(0);
                    let err_str_cvar =
                        ContextVarNode::from(err.expect_single().into_expr_err(loc)?);
                    Some(ErrType::RevertString(err_str_cvar))
                } else if assertion {
                    Some(ErrType::assertion())
                } else {
                    None
                };
                let cnode = ConcreteNode::from(self.add_node(Concrete::Bool(true)));
                let tmp_true = ContextVar::new_from_concrete(Loc::Implicit, ctx, cnode, self)
                    .into_expr_err(loc)?;
                let rhs = ExprRet::Single(self.add_node(tmp_true));
                self.handle_require_inner(arena, ctx, &req, &rhs, RangeOp::Eq, err, loc)
            }

            TestCommand(..) => self.interp_test_command(arena, ctx, next),

            // Looping
            While { .. } => self.interp_while(arena, ctx, stack, next),
            For { .. } => self.interp_for(arena, ctx, stack, next),
            Continue(loc) | Break(loc) => Err(ExprErr::Todo(
                loc,
                "Control flow expressions like break and continue are not currently supported"
                    .to_string(),
            )),

            // Pre and post increment/decrement
            PostIncrement(loc, ..)
            | PreIncrement(loc, ..)
            | PostDecrement(loc, ..)
            | PreDecrement(loc, ..) => self.interp_xxcrement(arena, ctx, next, loc),

            // Array
            ArrayTy(..) => self.interp_array_ty(arena, ctx, next),
            ArrayIndexAccess(_) => self.interp_array_idx(arena, ctx, next),
            ArraySlice(..) => self.interp_array_slice(arena, ctx, next),
            ArrayLiteral(..) => self.interp_array_lit(ctx, next),

            // Binary operators
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
            BitwiseNot(..) => self.interp_bit_not(arena, ctx, next),
            // Comparator
            Not(..) => self.interp_not(arena, ctx, next),
            Equal(loc)
            | NotEqual(loc)
            | Less(loc)
            | More(loc)
            | LessEqual(loc)
            | MoreEqual(loc)
            | And(loc, ..)
            | Or(loc) => self.interp_cmp(arena, ctx, loc, next),

            // Function calling
            MemberAccess(..) => self.interp_member_access(arena, ctx, stack, next, parse_idx),
            FunctionCall { .. } => self.interp_func_call(arena, ctx, stack, next, None, parse_idx),
            FunctionCallBlock(..) => Ok(()),
            NamedArgument(..) => Ok(()),
            NamedFunctionCall { .. } => {
                self.interp_named_func_call(arena, ctx, stack, next, parse_idx)
            }
            Return(..) => self.interp_return(arena, ctx, next),
            Revert(loc, custom, n) => {
                if custom {
                    let mut custom_err = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                    let err = custom_err.remove(0).expect_single().into_expr_err(loc)?;
                    ctx.add_return_node(loc, err.into(), self)
                        .into_expr_err(loc)?;
                } else if n == 1 {
                    let mut rev_string = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                    let err_str = rev_string.remove(0).expect_single().into_expr_err(loc)?;
                    let err_ty = ErrType::RevertString(err_str.into());
                    let ret = self.add_err_node(ctx, err_ty, loc)?;
                    ctx.add_return_node(loc, ret, self).into_expr_err(loc)?;
                } else {
                    let _ = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
                }

                ctx.kill(self, loc, KilledKind::Revert).into_expr_err(loc)
            }

            // Semi useless
            Super(..) => unreachable!(),
            Parameter(_, _, _) => Ok(()),
            Pop => {
                // let _ = ctx
                //     .pop_n_latest_exprs(1, Loc::Implicit, self)
                //     .into_expr_err(Loc::Implicit)?;
                Ok(())
            }
            Dup => {
                let mut res = ctx
                    .pop_n_latest_exprs(1, Loc::Implicit, self)
                    .into_expr_err(Loc::Implicit)?;
                let to_dup = res.remove(0);
                let duped = to_dup.clone();
                ctx.push_expr(to_dup, self).unwrap();
                ctx.push_expr(duped, self).unwrap();
                Ok(())
            }
            Swap => {
                let mut res = ctx
                    .pop_n_latest_exprs(2, Loc::Implicit, self)
                    .into_expr_err(Loc::Implicit)?;
                ctx.push_expr(res.remove(0), self).unwrap();
                ctx.push_expr(res.remove(0), self).unwrap();
                Ok(())
            }
            Emit(loc) => {
                let _ = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                Ok(())
            }
            Null(loc) => ctx.push_expr(ExprRet::Null, self).into_expr_err(loc),

            // Todo
            UnaryPlus(_) => todo!(),

            // Yul
            YulExpr(FlatYulExpr::YulStartBlock(s)) => {
                if self.current_asm_block() < s {
                    self.increment_asm_block();
                }
                Ok(())
            }
            YulExpr(yul @ FlatYulExpr::YulVariable(..)) => self.interp_yul_var(arena, ctx, yul),
            YulExpr(yul @ FlatYulExpr::YulFuncCall(..)) => {
                self.interp_yul_func_call(arena, ctx, stack, yul)
            }
            YulExpr(yul @ FlatYulExpr::YulSuffixAccess(..)) => self.interp_yul_suffix(ctx, yul),
            YulExpr(yul @ FlatYulExpr::YulAssign(..)) => self.interp_yul_assign(arena, ctx, yul),
            YulExpr(yul @ FlatYulExpr::YulFuncDef(..)) => {
                self.interp_yul_func_def(ctx, stack, yul, parse_idx)
            }
            YulExpr(yul @ FlatYulExpr::YulVarDecl(..)) => {
                self.interp_yul_var_decl(arena, ctx, stack, yul, parse_idx)
            }
            YulExpr(FlatYulExpr::YulEndBlock(s)) => {
                if self.current_asm_block() > s {
                    self.decrement_asm_block();
                }
                Ok(())
            }
        }?;

        if let Some(loc) = next.try_loc() {
            if ctx.kill_if_ret_killed(self, loc).into_expr_err(loc)? {
                return Ok(());
            }
        }
        Ok(())
    }

    fn interp_delete(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::Delete(loc) = next else {
            unreachable!()
        };

        let to_delete = ctx
            .pop_n_latest_exprs(1, loc, self)
            .into_expr_err(loc)?
            .swap_remove(0);

        self.delete_match(arena, ctx, to_delete, loc)
    }

    fn delete_match(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        to_delete: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match to_delete {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                let mut new_var = self
                    .advance_var_in_ctx(arena, cvar.into(), loc, ctx)
                    .unwrap();
                new_var.sol_delete_range(self).into_expr_err(loc)
            }
            ExprRet::Multi(inner) => inner
                .into_iter()
                .try_for_each(|i| self.delete_match(arena, ctx, i, loc)),
            ExprRet::Null => Ok(()),
        }
    }

    fn interp_this(&mut self, ctx: ContextNode, next: FlatExpr) -> Result<(), ExprErr> {
        let FlatExpr::This(loc) = next else {
            unreachable!()
        };

        let mut var = ContextVar::new_from_contract(
            loc,
            ctx.associated_contract(self).into_expr_err(loc)?,
            self,
        )
        .into_expr_err(loc)?;
        var.name = "this".to_string();
        var.display_name = "this".to_string();
        let cvar = self.add_node(Node::ContextVar(var));
        ctx.add_var(cvar.into(), self).into_expr_err(loc)?;
        self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
        ctx.push_expr(ExprRet::Single(cvar), self)
            .into_expr_err(loc)
    }

    fn interp_test_command(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::TestCommand(loc, cmd_str) = next else {
            unreachable!()
        };
        if let Some(cmd) = self.test_string_literal(cmd_str) {
            self.run_test_command(arena, ctx, cmd, loc);
        }
        Ok(())
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
        stack: &mut Vec<FlatExpr>,
        next: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::MemberAccess(loc, name) = next else {
            unreachable!()
        };

        // If the member access points to a library function, we need to keep the
        // member on the stack
        match ctx.take_expr_flag(self) {
            Some(ExprFlag::FunctionName {
                num_inputs,
                call_block_inputs,
                is_super,
                named_args,
                try_catch,
            }) => {
                if try_catch {
                    ctx.set_expr_flag(self, ExprFlag::Try);
                }
                let mut member_and_inputs = ctx
                    .pop_n_latest_exprs(num_inputs + call_block_inputs + 1, loc, self)
                    .into_expr_err(loc)?;

                let member = member_and_inputs.remove(member_and_inputs.len().saturating_sub(1));

                member_and_inputs.into_iter().rev().for_each(|input| {
                    ctx.push_expr(input, self).unwrap();
                });

                let maybe_names = if named_args {
                    let mut start = parse_idx;
                    let mut curr = &stack[start];
                    while !matches!(curr, FlatExpr::NamedFunctionCall { .. }) {
                        start += 1;
                        curr = &stack[start];
                    }
                    start -= num_inputs;
                    Some(self.get_named_args(stack, start, num_inputs))
                } else {
                    None
                };

                let member_idx = member.expect_single().into_expr_err(loc)?;

                let mut found_funcs = self
                    .find_func(
                        ctx,
                        name,
                        num_inputs,
                        &maybe_names,
                        is_super,
                        Some(member_idx),
                    )
                    .into_expr_err(loc)?;
                match found_funcs.len() {
                    0 => Err(ExprErr::FunctionNotFound(
                        loc,
                        "Member Function not found".to_string(),
                    )),
                    1 => {
                        let FindFunc {
                            func,
                            reordering,
                            was_lib_func,
                        } = found_funcs.swap_remove(0);

                        self.order_fn_inputs(ctx, num_inputs, reordering, loc)?;

                        if was_lib_func {
                            ctx.push_expr(member, self).into_expr_err(loc)?;
                            let mut stack_iter_mut = stack.iter_mut().skip(ctx.parse_idx(self));
                            let mut found = false;
                            while !found {
                                match stack_iter_mut.next() {
                                    Some(FlatExpr::FunctionCall {
                                        num_inputs: ref mut n,
                                        ..
                                    }) => {
                                        *n = num_inputs + 1;
                                        found = true;
                                    }
                                    Some(FlatExpr::NamedFunctionCall {
                                        num_inputs: ref mut n,
                                        ..
                                    }) => {
                                        *n = num_inputs + 1;
                                        found = true;
                                    }
                                    Some(_) | None => {}
                                }
                            }
                        } else {
                            let mut stack_iter_mut = stack.iter_mut().skip(ctx.parse_idx(self) - 1);
                            let mut found = false;
                            while !found {
                                match stack_iter_mut.next() {
                                    Some(FlatExpr::FunctionCall {
                                        maybe_target: ref mut ext,
                                        ..
                                    }) => {
                                        *ext = Some(member.expect_single().into_expr_err(loc)?);
                                        found = true;
                                    }
                                    Some(FlatExpr::NamedFunctionCall {
                                        maybe_target: ref mut ext,
                                        ..
                                    }) => {
                                        *ext = Some(member.expect_single().into_expr_err(loc)?);
                                        found = true;
                                    }
                                    Some(_) | None => {}
                                }
                            }
                        }

                        let as_var =
                            ContextVar::maybe_from_user_ty(self, loc, func.into()).unwrap();
                        let fn_var = ContextVarNode::from(self.add_node(as_var));
                        ctx.add_var(fn_var, self).into_expr_err(loc)?;
                        self.add_edge(fn_var, ctx, Edge::Context(ContextEdge::Variable));
                        ctx.push_expr(ExprRet::Single(fn_var.into()), self)
                            .into_expr_err(loc)
                    }
                    _ => {
                        let err_str = format!(
                            "Unable to disambiguate member function call, possible functions: {:?}",
                            found_funcs
                                .iter()
                                .map(|i| i.func.name(self).unwrap())
                                .collect::<Vec<_>>()
                        );
                        Err(ExprErr::FunctionNotFound(loc, err_str))
                    }
                }
            }
            _ => {
                let member = ctx
                    .pop_n_latest_exprs(1, loc, self)
                    .into_expr_err(loc)?
                    .swap_remove(0);
                let was_lib_func = self.member_access(arena, ctx, member.clone(), name, loc)?;
                if was_lib_func {
                    todo!("Got a library function without a function call?");
                }

                Ok(())
            }
        }
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

    fn interp_while(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        while_expr: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::While {
            loc,
            condition,
            body,
        } = while_expr
        else {
            unreachable!()
        };

        let loop_ctx = Context::add_loop_subctx(ctx, loc, self).into_expr_err(loc)?;

        // run the condition
        if condition > 0 {
            for _ in 0..condition {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        // run the body
        if body > 0 {
            for _ in 0..body {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        self.flat_apply_to_edges(
            loop_ctx,
            loc,
            arena,
            stack,
            &|analyzer: &mut Self,
              arena: &mut RangeArena<Elem<Concrete>>,
              loop_ctx: ContextNode,
              loc: Loc,
              _: &mut Vec<FlatExpr>| {
                analyzer.reset_vars(arena, ctx, loop_ctx, loc)
            },
        )?;

        let end = ctx.parse_idx(self) + condition + body;

        self.modify_edges(ctx, loc, &|analyzer, ctx| {
            ctx.underlying_mut(analyzer).unwrap().parse_idx = end;
            Ok(())
        })
    }

    fn interp_for(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        for_expr: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::For {
            loc,
            start,
            condition,
            after_each,
            body,
        } = for_expr
        else {
            unreachable!()
        };

        let loop_ctx = Context::add_loop_subctx(ctx, loc, self).into_expr_err(loc)?;

        // initiate the loop variable
        if start > 0 {
            for _ in 0..start {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        // run the condition
        if condition > 0 {
            for _ in 0..condition {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        // run the body
        if body > 0 {
            for _ in 0..body {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        // run the after each
        if after_each > 0 {
            for _ in 0..after_each {
                self.interpret_step(arena, loop_ctx, loc, stack)?;
            }
        }

        self.flat_apply_to_edges(
            loop_ctx,
            loc,
            arena,
            stack,
            &|analyzer: &mut Self,
              arena: &mut RangeArena<Elem<Concrete>>,
              loop_ctx: ContextNode,
              loc: Loc,
              _: &mut Vec<FlatExpr>| {
                analyzer.reset_vars(arena, ctx, loop_ctx, loc)
            },
        )?;

        let end = ctx.parse_idx(self) + start + condition + body + after_each;

        self.modify_edges(ctx, loc, &|analyzer, ctx| {
            ctx.underlying_mut(analyzer).unwrap().parse_idx = end;
            Ok(())
        })
    }

    fn interp_if(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
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

        let (true_subctx, false_subctx) =
            Context::add_fork_subctxs(self, ctx, loc, false).into_expr_err(loc)?;

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
                // println!("BOTH KILLED");
                // both have been killed, delete the child and dont process the bodies
                ctx.delete_child(self).into_expr_err(loc)?;
            }
            (true, false) => {
                // println!("TRUE KILLED");
                // the true context has been killed, delete child, process the false fork expression
                // in the parent context and parse the false body
                ctx.delete_child(self).into_expr_err(loc)?;

                // point the parse index of the parent ctx to the false body
                ctx.underlying_mut(self).unwrap().parse_idx =
                    ctx.parse_idx(self) + true_cond + false_cond + true_body;
                for _ in 0..false_body {
                    self.interpret_step(arena, ctx, loc, stack)?;
                }
            }
            (false, true) => {
                // the false context has been killed, delete child, process the true fork expression
                // in the parent context and parse the true body
                ctx.delete_child(self).into_expr_err(loc)?;

                // point the parse index of the parent ctx to the true body
                ctx.underlying_mut(self).unwrap().parse_idx =
                    ctx.parse_idx(self) + true_cond + false_cond;
                for _ in 0..true_body {
                    self.interpret_step(arena, ctx, loc, stack)?;
                }

                // skip false body
                self.modify_edges(ctx, loc, &|analyzer, ctx| {
                    ctx.skip_n_exprs(false_body, analyzer);
                    Ok(())
                })?;
            }
            (false, false) => {
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

                if let Some(cont) = true_subctx.underlying(self).unwrap().continuation_of() {
                    self.add_edge(
                        true_subctx,
                        cont,
                        Edge::Context(ContextEdge::Continue("TODO")),
                    );
                }

                if let Some(cont) = false_subctx.underlying(self).unwrap().continuation_of() {
                    self.add_edge(
                        false_subctx,
                        cont,
                        Edge::Context(ContextEdge::Continue("TODO")),
                    );
                }

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
                for _ in 0..false_body {
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

        if let Some(ExprFlag::Requirement(try_catch, with_str, assertion)) =
            ctx.peek_expr_flag(self)
        {
            let err = if with_str {
                let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
                let [err] = into_sized::<ExprRet, 1>(res);
                let err_str_cvar = ContextVarNode::from(err.expect_single().into_expr_err(loc)?);
                Some(ErrType::RevertString(err_str_cvar))
            } else if assertion {
                Some(ErrType::assertion())
            } else {
                None
            };

            if try_catch {
                ctx.set_expr_flag(self, ExprFlag::Try);
            } else {
                ctx.take_expr_flag(self);
            }

            match cmp {
                FlatExpr::Equal(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Eq, err, loc)
                }
                FlatExpr::NotEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Neq, err, loc)
                }
                FlatExpr::Less(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Lt, err, loc)
                }
                FlatExpr::More(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Gt, err, loc)
                }
                FlatExpr::LessEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Lte, err, loc)
                }
                FlatExpr::MoreEqual(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::Gte, err, loc)
                }
                FlatExpr::Or(..) => {
                    let lhs = ContextVarNode::from(lhs.expect_single().into_expr_err(loc)?);
                    let rhs = ContextVarNode::from(rhs.expect_single().into_expr_err(loc)?);
                    let elem = Elem::Expr(RangeExpr::new(lhs.into(), RangeOp::Or, rhs.into()));
                    let range = SolcRange::new(elem.clone(), elem, vec![]);
                    let new_lhs_underlying = ContextVar {
                        loc: Some(loc),
                        name: format!(
                            "tmp{}({} {} {})",
                            ctx.new_tmp(self).into_expr_err(loc)?,
                            lhs.name(self).into_expr_err(loc)?,
                            RangeOp::Or,
                            rhs.name(self).into_expr_err(loc)?
                        ),
                        display_name: format!(
                            "({} {} {})",
                            lhs.display_name(self).into_expr_err(loc)?,
                            RangeOp::Or,
                            rhs.display_name(self).into_expr_err(loc)?
                        ),
                        storage: None,
                        is_tmp: true,
                        is_symbolic: lhs.is_symbolic(self).into_expr_err(loc)?
                            || rhs.is_symbolic(self).into_expr_err(loc)?,
                        is_return: false,
                        tmp_of: Some(TmpConstruction::new(lhs, RangeOp::Or, Some(rhs))),
                        dep_on: {
                            let mut deps = lhs.dependent_on(self, true).into_expr_err(loc)?;
                            deps.extend(rhs.dependent_on(self, true).into_expr_err(loc)?);
                            Some(deps)
                        },
                        is_fundamental: None,
                        ty: VarType::BuiltIn(
                            self.builtin_or_add(Builtin::Bool).into(),
                            Some(range),
                        ),
                    };
                    let or_var = ContextVarNode::from(self.add_node(new_lhs_underlying));
                    let node = self.add_concrete_var(ctx, Concrete::Bool(true), loc)?;
                    ctx.add_var(node, self).into_expr_err(loc)?;
                    self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                    self.handle_require_inner(
                        arena,
                        ctx,
                        &ExprRet::Single(or_var.into()),
                        &ExprRet::Single(node.into()),
                        RangeOp::Eq,
                        err,
                        loc,
                    )
                }
                FlatExpr::And(..) => {
                    self.handle_require_inner(arena, ctx, &lhs, &rhs, RangeOp::And, err, loc)
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
                FlatExpr::And(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::And, &rhs),
                FlatExpr::Or(..) => self.cmp_inner(arena, ctx, loc, &lhs, RangeOp::Or, &rhs),
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

        if let Some(ExprFlag::FunctionName { try_catch, .. }) = ctx.peek_expr_flag(self) {
            ctx.take_expr_flag(self);
            if try_catch {
                ctx.set_expr_flag(self, ExprFlag::Try);
            }
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
            let mut ret = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            self.return_match(arena, ctx, loc, ret.swap_remove(0), 0);
            Ok(())
        } else {
            self.return_match(arena, ctx, loc, ExprRet::CtxKilled(KilledKind::Ended), 0);
            Ok(())
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

        match ctx.take_expr_flag(self) {
            Some(ExprFlag::FunctionName {
                num_inputs,
                call_block_inputs: _,
                is_super,
                named_args,
                try_catch,
            }) => {
                if try_catch {
                    ctx.set_expr_flag(self, ExprFlag::Try);
                }
                let maybe_names = if named_args {
                    let start = parse_idx + 1;
                    Some(self.get_named_args(stack, start, num_inputs))
                } else {
                    None
                };

                let mut found_funcs = self
                    .find_func(ctx, name, num_inputs, &maybe_names, is_super, None)
                    .into_expr_err(loc)?;
                match found_funcs.len() {
                    0 => {
                        // try a regular `variable` lookup
                    }
                    1 => {
                        let FindFunc {
                            func,
                            reordering,
                            was_lib_func: _,
                        } = found_funcs.swap_remove(0);
                        self.order_fn_inputs(ctx, num_inputs, reordering, loc)?;
                        let as_var =
                            ContextVar::maybe_from_user_ty(self, loc, func.into()).unwrap();
                        let fn_var = ContextVarNode::from(self.add_node(as_var));
                        ctx.add_var(fn_var, self).into_expr_err(loc)?;
                        self.add_edge(fn_var, ctx, Edge::Context(ContextEdge::Variable));
                        return ctx
                            .push_expr(ExprRet::Single(fn_var.into()), self)
                            .into_expr_err(loc);
                    }
                    _ => {
                        let err_str = format!(
                            "Unable to disambiguate member function call, possible functions: {:?}",
                            found_funcs
                                .iter()
                                .map(|i| i.func.name(self).unwrap())
                                .collect::<Vec<_>>()
                        );
                        return Err(ExprErr::FunctionNotFound(loc, err_str));
                    }
                }
            }
            Some(other) => {
                ctx.set_expr_flag(self, other);
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

    fn order_fn_inputs(
        &mut self,
        ctx: ContextNode,
        n: usize,
        reordering: BTreeMap<usize, usize>,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        // reorder the inputs now that we have the function
        let inputs = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
        let mut tmp_inputs = vec![];
        tmp_inputs.resize(n, ExprRet::Null);
        inputs.into_iter().enumerate().for_each(|(i, ret)| {
            let target_idx = reordering[&i];
            tmp_inputs[target_idx] = ret;
        });

        // we reverse it because of how they are popped off the stack in the actual
        // function call
        tmp_inputs
            .into_iter()
            .rev()
            .try_for_each(|i| ctx.push_expr(i, self))
            .into_expr_err(loc)
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
        let FlatExpr::ArrayTy(loc, sized) = arr_ty else {
            unreachable!()
        };
        if sized {
            let mut res = ctx.pop_n_latest_exprs(2, loc, self).into_expr_err(loc)?;
            let arr_ty = res.swap_remove(0);
            let size_var =
                ContextVarNode::from(res.swap_remove(0).expect_single().into_expr_err(loc)?);
            assert!(size_var.is_const(self, arena).into_expr_err(loc)?);
            let size_elem = size_var
                .evaled_range_max(self, arena)
                .into_expr_err(loc)?
                .unwrap();
            let size = size_elem.maybe_concrete().unwrap().val.uint_val().unwrap();
            self.match_ty(ctx, loc, arr_ty, Some(size))
        } else {
            let res = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            let [arr_ty] = into_sized(res);
            self.match_ty(ctx, loc, arr_ty, None)
        }
    }

    fn interp_array_slice(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        arr_slice: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::ArraySlice(loc, has_start, has_end) = arr_slice else {
            unreachable!()
        };

        let to_pop = 1 + has_start as usize + has_end as usize;
        let mut res = ctx
            .pop_n_latest_exprs(to_pop, loc, self)
            .into_expr_err(loc)?;

        let arr = res.swap_remove(0);
        let end = if has_end {
            Some(res.swap_remove(0))
        } else {
            None
        };
        let start = if has_start {
            Some(res.swap_remove(0))
        } else {
            None
        };

        self.slice_inner(arena, ctx, arr, start, end, loc)
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

    fn interp_array_lit(&mut self, ctx: ContextNode, arr_lit: FlatExpr) -> Result<(), ExprErr> {
        let FlatExpr::ArrayLiteral(loc, n) = arr_lit else {
            unreachable!()
        };

        let res = ctx.pop_n_latest_exprs(n, loc, self).into_expr_err(loc)?;
        let ty = VarType::try_from_idx(self, res[0].expect_single().into_expr_err(loc)?).unwrap();

        let ty = Builtin::SizedArray(U256::from(n), ty);
        let bn_node = BuiltInNode::from(self.builtin_or_add(ty));

        let var = ContextVar::new_from_builtin(loc, bn_node, self).into_expr_err(loc)?;
        let arr = ContextVarNode::from(self.add_node(var));

        let kv_pairs = res
            .iter()
            .enumerate()
            .map(|(i, input)| {
                let i_var = ContextVarNode::from(input.expect_single().unwrap());
                let idx = self.add_concrete_var(ctx, Concrete::Uint(256, U256::from(i)), loc)?;
                self.add_edge(idx, ctx, Edge::Context(ContextEdge::Variable));
                Ok((Elem::from(idx), Elem::from(i_var)))
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;

        let len = RangeConcrete {
            val: Concrete::from(U256::from(n)),
            loc,
        };
        let range_elem: Elem<Concrete> =
            Elem::ConcreteDyn(RangeDyn::new(Elem::from(len), kv_pairs, loc));

        arr.ty_mut(self)
            .into_expr_err(loc)?
            .set_range(range_elem.into())
            .into_expr_err(loc)?;
        ctx.push_expr(
            ExprRet::SingleLiteral(arr.latest_version(self).into()),
            self,
        )
        .into_expr_err(loc)
    }

    fn interp_named_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        func_call: FlatExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatExpr::NamedFunctionCall { num_inputs: n, .. } = func_call else {
            unreachable!()
        };

        let sub_start = match ctx.peek_expr_flag(self) {
            Some(ExprFlag::New(_)) => 1 + n,
            _ => n,
        };

        let names_start = parse_idx.saturating_sub(sub_start);
        let names = self.get_named_args(stack, names_start, n);

        self.interp_func_call(arena, ctx, stack, func_call, Some(names), parse_idx)
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
        stack: &mut Vec<FlatExpr>,
        func_call: FlatExpr,
        input_names: Option<Vec<&str>>,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let (loc, ext, n, call_block_inputs) = match func_call {
            FlatExpr::FunctionCall {
                loc,
                maybe_target,
                num_inputs,
                num_call_block_inputs,
            }
            | FlatExpr::NamedFunctionCall {
                loc,
                maybe_target,
                num_inputs,
                num_call_block_inputs,
            } => (loc, maybe_target, num_inputs, num_call_block_inputs),
            _ => unreachable!(),
        };

        let mut try_catch = false;
        let mut is_new_call = false;
        match ctx.peek_expr_flag(self) {
            Some(ExprFlag::New(new_try_catch)) => {
                let _ = ctx.take_expr_flag(self);
                is_new_call = true;
                try_catch = new_try_catch;
            }
            Some(ExprFlag::Try) => {
                // only take the try flag if
                if ext.is_some() {
                    let _ = ctx.take_expr_flag(self);
                    try_catch = true;
                }
            }
            _ => {}
        };

        // println!("TRY CATCH: {try_catch}");

        let mut func_and_inputs = ctx
            .pop_n_latest_exprs(n + 1 + call_block_inputs, loc, self)
            .into_expr_err(loc)?;

        let mut inputs = func_and_inputs.split_off(1);
        let [func_ret] = into_sized(func_and_inputs);
        let func = func_ret.expect_single().into_expr_err(loc)?;
        let call_args = inputs.split_off(n);

        let env = if !call_args.is_empty() {
            let msg = self.msg().underlying(self).unwrap().clone();
            let mut env_ctx = EnvCtx::from_msg(self, &msg, loc, ctx).into_expr_err(loc)?;

            // walk backwards in the stack till we see function call block
            let start = {
                let mut test_idx = parse_idx;
                let mut curr = &stack[test_idx];
                while !matches!(curr, FlatExpr::FunctionCallBlock(..)) {
                    test_idx -= 1;
                    curr = &stack[test_idx];
                }

                test_idx - call_block_inputs
            };

            let names = self.get_named_args(stack, start, call_block_inputs);
            names
                .iter()
                .rev()
                .enumerate()
                .try_for_each(|(i, name)| {
                    let input = call_args[i].expect_single().unwrap();
                    let mut var = ContextVarNode::from(input).underlying(self)?.clone();
                    var.name = EnvCtx::get_name(name).unwrap();
                    var.display_name.clone_from(&var.name);
                    let var_node = self.add_node(var);
                    env_ctx.set(name, var_node);
                    Ok(())
                })
                .into_expr_err(loc)?;
            Some(env_ctx)
        } else {
            let msg = self.msg().underlying(self).unwrap().clone();
            Some(EnvCtx::from_msg(self, &msg, loc, ctx).into_expr_err(loc)?)
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
                        inputs.iter().enumerate().for_each(|(i, ret)| {
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
            res?.unwrap_or(inputs)
        } else {
            vec![]
        };

        let inputs = ExprRet::Multi(inputs);

        if self.debug_stack() {
            tracing::trace!("inputs: {}", inputs.debug_str_ranged(self, arena));
        }

        if is_new_call {
            return self.new_call_inner(arena, ctx, func, inputs, loc, env);
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
            VarType::User(TypeNode::Error(en), _) => {
                self.construct_err_inner(arena, ctx, en, inputs, loc)
            }
            VarType::User(TypeNode::Contract(c), _) => {
                self.construct_contract_inner(arena, ctx, c, inputs, loc)
            }
            VarType::User(TypeNode::Func(s), _) => {
                if self
                    .builtin_fn_nodes()
                    .iter()
                    .any(|(_, v)| *v == s.0.into())
                {
                    // its a builtin function call
                    self.call_builtin(arena, ctx, &s.name(self).into_expr_err(loc)?, inputs, loc)
                } else {
                    let id = ext.map(|i| ContractId::Address(ContextVarNode::from(i)));
                    self.func_call(arena, ctx, loc, &inputs, s, None, None, env, id, try_catch)
                }
            }
            VarType::BuiltIn(bn, _) => {
                // cast to type
                let Node::Builtin(builtin) = self.node(bn).clone() else {
                    unreachable!()
                };
                self.cast_inner(arena, ctx, ty, &builtin, inputs, loc)
            }
            VarType::User(TypeNode::Unresolved(idx), _) => Err(ExprErr::ParseError(
                loc,
                format!(
                    "Could not call function: {:?}. The inputs may be wrong, or the this is a bug.",
                    self.node(idx)
                ),
            )),
            VarType::Concrete(cn) => {
                let builtin = cn.underlying(self).unwrap().as_builtin();
                self.cast_inner(arena, ctx, ty, &builtin, inputs, loc)
            }
            e => Err(ExprErr::Todo(loc, format!("Unhandled ty: {e:?}"))),
        }
    }

    fn interp_negatable_literal(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        lit: FlatExpr,
    ) -> Result<(), ExprErr> {
        let mut negate = false;
        match ctx.take_expr_flag(self) {
            Some(ExprFlag::Negate(try_catch)) => {
                if try_catch {
                    ctx.set_expr_flag(self, ExprFlag::Try);
                }
                negate = true;
            }
            Some(other) => ctx.set_expr_flag(self, other),
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

        let ret = ctx
            .pop_n_latest_exprs(1, loc, self)
            .into_expr_err(loc)?
            .swap_remove(0);
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
    }

    fn interp_yul_func_def(
        &mut self,
        ctx: ContextNode,
        stack: &mut Vec<FlatExpr>,
        next: FlatYulExpr,
        parse_idx: usize,
    ) -> Result<(), ExprErr> {
        let FlatYulExpr::YulFuncDef(loc, name, num) = next else {
            unreachable!()
        };

        let end = parse_idx + 1 + num;
        let exprs = stack[parse_idx + 1..end].to_vec();
        let fn_node = ctx.associated_fn(self).into_expr_err(loc)?;
        let yul_fn = self.add_node(YulFunction::new(exprs, name, loc));
        self.add_edge(yul_fn, fn_node, Edge::YulFunction(self.current_asm_block()));
        ctx.underlying_mut(self).into_expr_err(loc)?.parse_idx = end;
        Ok(())
    }

    fn interp_yul_suffix(&mut self, ctx: ContextNode, next: FlatYulExpr) -> Result<(), ExprErr> {
        let FlatYulExpr::YulSuffixAccess(loc, name) = next else {
            unreachable!()
        };

        let member = ctx
            .pop_n_latest_exprs(1, loc, self)
            .into_expr_err(loc)?
            .remove(0);
        match name {
            "slot" => {
                let slot = self.slot(ctx, loc, member.expect_single().into_expr_err(loc)?.into());
                ctx.push_expr(ExprRet::Single(slot.0.into()), self)
                    .into_expr_err(loc)
            }
            _ => Err(ExprErr::Todo(
                loc,
                format!("Yul suffix access {name} is not supported"),
            )),
        }
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
        if let Some(child) = ctx.underlying(self).into_expr_err(loc)?.child {
            match child {
                CallFork::Call(call) => {
                    self.flat_apply_to_edges(call, loc, arena, stack, closure)?;
                }
                CallFork::Fork(w1, w2) => {
                    self.flat_apply_to_edges(w1, loc, arena, stack, closure)?;
                    self.flat_apply_to_edges(w2, loc, arena, stack, closure)?;
                }
            }
        } else if !ctx.is_ended(self).into_expr_err(loc)? {
            closure(self, arena, ctx, loc, stack)?;
        }
        Ok(())
    }
}

fn into_sized<T, const N: usize>(v: Vec<T>) -> [T; N] {
    v.try_into()
        .unwrap_or_else(|v: Vec<T>| panic!("Expected a Vec of length {} but it was {}", N, v.len()))
}
