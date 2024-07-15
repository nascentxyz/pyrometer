use crate::{
    context_builder::ContextBuilder,
    func_call::{
        func_caller::FuncCaller, internal_call::InternalFuncCaller,
        intrinsic_call::IntrinsicFuncCaller,
    },
    ExprTyParser,
};
use graph::{
    elem::{Elem, RangeOp},
    nodes::{
        Builtin, Concrete, Context, ContextNode, ContextVar, ContextVarNode, ExprRet, FunctionNode,
    },
    AnalyzerBackend, ContextEdge, Edge, Node, VarType,
};

use shared::{
    string_to_static, AnalyzerLike, ExprErr, ExprFlag, FlatExpr, IntoExprErr, RangeArena,
    StorageLocation,
};
use solang_parser::pt::Identifier;
use solang_parser::pt::{Expression, Loc, Statement, Type};

impl<T> Flatten for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
}

pub trait Flatten:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
    fn traverse_statement(&mut self, stmt: &Statement) {
        use Statement::*;

        match stmt {
            Block {
                loc: _,
                unchecked: _,
                statements,
            } => {
                for statement in statements {
                    // self.set_unchecked(unchecked);
                    self.traverse_statement(statement);
                }
                // self.set_unchecked(false);
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let lhs = var_decl.ty.clone();
                if let Some(rhs) = maybe_expr {
                    self.traverse_expression(rhs);
                }
                self.traverse_expression(&lhs);
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
            If(loc, if_expr, true_body, None) => {
                self.push_expr(FlatExpr::If(*loc));
                self.traverse_expression(if_expr);
                self.push_expr(FlatExpr::EndIfCond);
                self.traverse_statement(true_body);
                self.push_expr(FlatExpr::EndIfTrue);
            }
            If(loc, if_expr, true_body, Some(false_body)) => {
                self.push_expr(FlatExpr::IfElse(*loc));
                self.traverse_expression(if_expr);
                self.push_expr(FlatExpr::EndIfCond);
                self.traverse_statement(true_body);
                self.push_expr(FlatExpr::EndIfTrue);
                self.traverse_statement(false_body);
                self.push_expr(FlatExpr::EndIfElseFalse);
            }
            While(loc, cond, body) => {}
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {}
            DoWhile(loc, while_stmt, while_expr) => {}
            Expression(loc, expr) => {
                self.traverse_expression(&expr);
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
                    self.traverse_expression(ret_expr);
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

    fn traverse_expression(&mut self, parent_expr: &Expression) {
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
                self.push_expr(FlatExpr::from(parent_expr));
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
                self.traverse_expression(expr);
                self.push_expr(FlatExpr::from(parent_expr));
            }

            New(new_loc, expr) => {
                match &**expr {
                    FunctionCall(func_loc, func_expr, input_exprs) => {
                        input_exprs.iter().rev().for_each(|expr| {
                            self.traverse_expression(expr);
                        });

                        self.traverse_expression(func_expr);
                        self.push_expr(FlatExpr::New(*new_loc));
                        self.push_expr(FlatExpr::FunctionCall(*func_loc, input_exprs.len()));
                    }
                    NamedFunctionCall(loc, func_expr, input_args) => {
                        todo!();
                    }
                    _ => {
                        // add error
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
            | AssignDivide(_, lhs, rhs)
            | Modulo(_, lhs, rhs)
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
                self.traverse_expression(rhs);
                self.traverse_expression(lhs);
                self.push_expr(FlatExpr::from(parent_expr));
            }

            List(_, params) => {
                params.iter().for_each(|(loc, maybe_param)| {
                    if let Some(param) = maybe_param {
                        self.traverse_expression(&param.ty);
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
                        self.push_expr(FlatExpr::Null(*loc));
                    }
                });
                self.push_expr(FlatExpr::from(parent_expr));
            }
            // array
            ArraySubscript(loc, ty_expr, None) => {
                self.traverse_expression(ty_expr);
                self.push_expr(FlatExpr::ArrayTy(*loc));
            }
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.traverse_expression(index_expr);
                self.traverse_expression(ty_expr);
                self.push_expr(FlatExpr::ArrayIndexAccess(*loc));
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {}
            ArraySlice(loc, lhs_expr, maybe_middle_expr, maybe_rhs) => {}
            ArrayLiteral(loc, _) => {}

            // Function calls
            FunctionCallBlock(loc, func_expr, call_block) => {
                self.traverse_statement(call_block);
                self.traverse_expression(func_expr);
                self.push_expr(FlatExpr::FunctionCallBlock(*loc));
            }
            NamedFunctionCall(loc, func_expr, input_args) => {}
            FunctionCall(loc, func_expr, input_exprs) => {
                input_exprs.iter().rev().for_each(|expr| {
                    self.traverse_expression(expr);
                });

                self.push_expr(FlatExpr::FunctionCallName(input_exprs.len()));
                self.traverse_expression(func_expr);
                self.push_expr(FlatExpr::FunctionCall(*loc, input_exprs.len()));
            }
            // member
            This(loc) => self.push_expr(FlatExpr::This(*loc)),
            MemberAccess(loc, member_expr, ident) => {}

            // Misc.
            Type(..) => self.push_expr(FlatExpr::from(parent_expr)),
        }
    }

    fn interpret(
        &mut self,
        func: FunctionNode,
        body_loc: Loc,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        let stack = std::mem::take(self.expr_stack_mut());

        tracing::trace!("stack: {stack:#?}");
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

        for next in stack {
            let res = self.apply_to_edges(
                ctx,
                body_loc,
                arena,
                &|analyzer: &mut Self,
                  arena: &mut RangeArena<Elem<Concrete>>,
                  ctx: ContextNode,
                  _: Loc| analyzer.interpret_expr(arena, ctx, next),
            );

            self.add_if_err(res);
        }
    }

    fn interpret_expr(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        next: FlatExpr,
    ) -> Result<(), ExprErr> {
        use FlatExpr::*;
        tracing::trace!("parsing {:?} in context {}", next, ctx.path(self));
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
            ArrayTy(..) => self.interp_array_ty(arena, ctx, next),

            FunctionCall(..) => self.interp_func_call(arena, ctx, next),

            // Comparator
            Equal(loc) | NotEqual(loc) | Less(loc) | More(loc) | LessEqual(loc)
            | MoreEqual(loc) => self.interp_cmp(arena, ctx, loc, next),

            If(..) => Ok(()),
            IfElse(..) => Ok(()),
            other => {
                tracing::trace!("unhandled: {other:?}");
                Ok(())
            }
        }
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
        if !nonempty {
            let ret = ctx.pop_n_latest_exprs(1, loc, self).into_expr_err(loc)?;
            self.return_match(arena, ctx, &loc, ret.first().unwrap(), 0);
            Ok(())
        } else {
            ctx.propogate_end(self).into_expr_err(loc)
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

        if let Some(ExprFlag::FunctionName(n)) = self.take_expr_flag() {
            let maybe_fn = self
                .find_func(arena, ctx, name.to_string(), n)
                .into_expr_err(loc)?;
            if let Some(fn_node) = maybe_fn {
                let as_var = ContextVar::maybe_from_user_ty(self, loc, fn_node.into()).unwrap();
                let fn_var = ContextVarNode::from(self.add_node(as_var));
                ctx.add_var(fn_var, self).into_expr_err(loc)?;
                self.add_edge(fn_var, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(fn_var.into()), self)
                    .into_expr_err(loc)
            } else {
                Ok(())
            }
        } else {
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

    fn interp_func_call(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        func_call: FlatExpr,
    ) -> Result<(), ExprErr> {
        let FlatExpr::FunctionCall(loc, n) = func_call else {
            unreachable!()
        };

        let func_and_inputs = ctx
            .pop_n_latest_exprs(n + 1, loc, self)
            .into_expr_err(loc)?;

        let inputs = ExprRet::Multi(if n > 0 {
            func_and_inputs[1..].to_vec()
        } else {
            vec![]
        });

        match self.take_expr_flag() {
            Some(ExprFlag::New) => {
                let ty = func_and_inputs
                    .first()
                    .unwrap()
                    .expect_single()
                    .into_expr_err(loc)?;
                return self.new_call_inner(arena, loc, ty, inputs, ctx);
            }
            Some(other) => self.set_expr_flag(other),
            _ => {}
        }

        let func = ContextVarNode::from(
            func_and_inputs
                .first()
                .unwrap()
                .expect_single()
                .into_expr_err(loc)?,
        );

        let ty = func.ty(self).into_expr_err(loc)?;
        if let Some(func_node) = ty.func_node(self) {
            self.func_call(arena, ctx, loc, &inputs, func_node, None, None)
        } else {
            Ok(())
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
}

fn into_sized<T, const N: usize>(v: Vec<T>) -> [T; N] {
    v.try_into()
        .unwrap_or_else(|v: Vec<T>| panic!("Expected a Vec of length {} but it was {}", N, v.len()))
}
