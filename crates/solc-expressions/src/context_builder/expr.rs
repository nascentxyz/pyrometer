use crate::{
    context_builder::ContextBuilder, func_call::func_caller::FuncCaller, variable::Variable,
    ExprErr, ExprTyParser, IntoExprErr,
};

use graph::{
    elem::*,
    nodes::{Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node,
};

use ethers_core::types::I256;
use solang_parser::{
    helpers::CodeLocation,
    pt::{Expression, Loc},
};

impl<T> ExpressionParser for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
}

/// Solidity expression parser
pub trait ExpressionParser:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + ExprTyParser
{
    /// Perform setup for parsing an expression
    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        if !ctx.killed_or_ret(self).unwrap() {
            let edges = ctx.live_edges(self).into_expr_err(expr.loc())?;
            if edges.is_empty() {
                self.parse_ctx_expr_inner(expr, ctx)
            } else {
                edges
                    .iter()
                    .try_for_each(|fork_ctx| self.parse_ctx_expr(expr, *fork_ctx))?;
                Ok(())
            }
        } else {
            Ok(())
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(ctx = %ctx.path(self).replace('.', "\n\t.")))]
    /// Perform parsing of an expression
    fn parse_ctx_expr_inner(&mut self, expr: &Expression, ctx: ContextNode) -> Result<(), ExprErr> {
        use Expression::*;
        // tracing::trace!(
        //     "ctx: {}, current stack: {:?}, \nexpr: {:?}\n",
        //     ctx.underlying(self).unwrap().path,
        //     ctx.underlying(self)
        //         .unwrap()
        //         .expr_ret_stack
        //         .iter()
        //         .map(|i| i.debug_str(self))
        //         .collect::<Vec<_>>(),
        //     expr
        // );
        match expr {
            // literals
            NumberLiteral(loc, int, exp, _unit) => self.number_literal(ctx, *loc, int, exp, false),
            AddressLiteral(loc, addr) => self.address_literal(ctx, *loc, addr),
            StringLiteral(lits) => lits
                .iter()
                .try_for_each(|lit| self.string_literal(ctx, lit.loc, &lit.string)),
            BoolLiteral(loc, b) => self.bool_literal(ctx, *loc, *b),
            HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, false),
            HexLiteral(hexes) => self.hex_literals(ctx, hexes),
            RationalNumberLiteral(loc, integer, fraction, exp, unit) => {
                self.rational_number_literal(ctx, *loc, integer, fraction, exp, unit)
            }
            Negate(_loc, expr) => match &**expr {
                NumberLiteral(loc, int, exp, _unit) => {
                    self.number_literal(ctx, *loc, int, exp, true)
                }
                HexNumberLiteral(loc, b, _unit) => self.hex_num_literal(ctx, *loc, b, true),
                e => {
                    self.parse_ctx_expr(e, ctx)?;
                    self.apply_to_edges(ctx, e.loc(), &|analyzer, ctx, loc| {
                        tracing::trace!("Negate variable pop");
                        let Some(rhs_paths) =
                            ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?
                        else {
                            return Err(ExprErr::NoRhs(
                                loc,
                                "No variable present to negate".to_string(),
                            ));
                        };
                        if matches!(rhs_paths, ExprRet::CtxKilled(_)) {
                            ctx.push_expr(rhs_paths, analyzer).into_expr_err(loc)?;
                            return Ok(());
                        }

                        // Solidity is dumb and used to allow negation of unsigned integers.
                        // That means we have to cast this as a int256.
                        let var = rhs_paths.expect_single().into_expr_err(loc)?;

                        let zero =
                            analyzer.add_node(Node::Concrete(Concrete::from(I256::from(0i32))));
                        let zero = ContextVar::new_from_concrete(
                            Loc::Implicit,
                            ctx,
                            zero.into(),
                            analyzer,
                        )
                        .into_expr_err(loc)?;
                        let zero = analyzer.add_node(Node::ContextVar(zero));
                        let new_underlying = ContextVarNode::from(var)
                            .underlying(analyzer)
                            .into_expr_err(loc)?
                            .clone()
                            .as_cast_tmp(loc, ctx, Builtin::Int(256), analyzer)
                            .into_expr_err(loc)?;
                        let node = analyzer.add_node(Node::ContextVar(new_underlying));
                        ctx.add_var(node.into(), analyzer).into_expr_err(loc)?;
                        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));

                        ContextVarNode::from(node)
                            .cast_from(&ContextVarNode::from(zero), analyzer)
                            .into_expr_err(loc)?;

                        let lhs_paths = ExprRet::Single(zero);
                        analyzer.op_match(
                            ctx,
                            loc,
                            &lhs_paths,
                            &ExprRet::Single(
                                ContextVarNode::from(node).latest_version(analyzer).into(),
                            ),
                            RangeOp::Sub(true),
                            false,
                        )
                    })
                } // e => todo!("UnaryMinus unexpected rhs: {e:?}"),
            },
            UnaryPlus(_loc, e) => todo!("UnaryPlus unexpected rhs: {e:?}"),

            // Binary ops
            Power(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Exp, false)
            }
            Add(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Add(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignAdd(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Add(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Subtract(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Sub(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignSubtract(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Sub(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Multiply(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Mul(ctx.unchecked(self).into_expr_err(*loc)?),
                false,
            ),
            AssignMultiply(loc, lhs_expr, rhs_expr) => self.op_expr(
                *loc,
                lhs_expr,
                rhs_expr,
                ctx,
                RangeOp::Mul(ctx.unchecked(self).into_expr_err(*loc)?),
                true,
            ),
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div(false), false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div(false), true)
            }
            Modulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mod, false)
            }
            AssignModulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mod, true)
            }
            ShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shl, false)
            }
            AssignShiftLeft(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shl, true)
            }
            ShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shr, false)
            }
            AssignShiftRight(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Shr, true)
            }
            ConditionalOperator(loc, if_expr, true_expr, false_expr) => {
                self.cond_op_expr(*loc, if_expr, true_expr, false_expr, ctx)
            }

            // Bitwise ops
            BitwiseAnd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitAnd, false)
            }
            AssignAnd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitAnd, true)
            }
            BitwiseXor(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitXor, false)
            }
            AssignXor(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitXor, true)
            }
            BitwiseOr(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitOr, false)
            }
            AssignOr(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::BitOr, true)
            }
            BitwiseNot(loc, lhs_expr) => self.bit_not(*loc, lhs_expr, ctx),

            // assign
            Assign(loc, lhs_expr, rhs_expr) => self.assign_exprs(*loc, lhs_expr, rhs_expr, ctx),
            List(loc, params) => self.list(ctx, *loc, params),
            // array
            ArraySubscript(_loc, ty_expr, None) => self.array_ty(ty_expr, ctx),
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.index_into_array(*loc, ty_expr, index_expr, ctx)
            }
            ArraySlice(loc, _lhs_expr, _maybe_middle_expr, _maybe_rhs) => Err(ExprErr::Todo(
                *loc,
                "Array slicing not currently supported".to_string(),
            )),
            ArrayLiteral(loc, _) => Err(ExprErr::Todo(
                *loc,
                "Array literal not currently supported".to_string(),
            )),

            // Comparator
            Equal(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Eq, rhs, ctx),
            NotEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Neq, rhs, ctx),
            Less(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Lt, rhs, ctx),
            More(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Gt, rhs, ctx),
            LessEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Lte, rhs, ctx),
            MoreEqual(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Gte, rhs, ctx),

            // Logical
            Not(loc, expr) => self.not(*loc, expr, ctx),
            And(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::And, rhs, ctx),
            Or(loc, lhs, rhs) => self.cmp(*loc, lhs, RangeOp::Or, rhs, ctx),

            // Function calls
            FunctionCallBlock(loc, _func_expr, _input_exprs) => {
                // TODO: update msg node
                Err(ExprErr::Todo(
                    *loc,
                    "Function call block is unsupported. We shouldn't have hit this code path"
                        .to_string(),
                ))
            }
            NamedFunctionCall(loc, func_expr, input_args) => {
                self.named_fn_call_expr(ctx, loc, func_expr, input_args)
            }
            FunctionCall(loc, func_expr, input_exprs) => {
                let updated_func_expr = match **func_expr {
                    FunctionCallBlock(_loc, ref inner_func_expr, ref call_block) => {
                        // we dont currently handle the `{value: .. gas: ..}` msg updating
                        self.add_expr_err(ExprErr::FunctionCallBlockTodo(call_block.loc(), "Function call block is currently unsupported. Relevant changes on `msg` will not take effect".to_string()));
                        inner_func_expr.clone()
                    }
                    _ => func_expr.clone(),
                };

                self.fn_call_expr(ctx, loc, &updated_func_expr, input_exprs)
            }
            // member
            New(_loc, expr) => self.parse_ctx_expr(expr, ctx),
            This(loc) => {
                let var = ContextVar::new_from_contract(
                    *loc,
                    ctx.associated_contract(self).into_expr_err(*loc)?,
                    self,
                )
                .into_expr_err(*loc)?;
                let cvar = self.add_node(Node::ContextVar(var));
                ctx.add_var(cvar.into(), self).into_expr_err(*loc)?;
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                ctx.push_expr(ExprRet::Single(cvar), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            MemberAccess(loc, member_expr, ident) => {
                self.member_access(*loc, member_expr, ident, ctx)
            }

            Delete(loc, expr) => {
                fn delete_match(
                    ctx: ContextNode,
                    loc: &Loc,
                    analyzer: &mut (impl GraphBackend
                              + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr>),
                    ret: ExprRet,
                ) {
                    match ret {
                        ExprRet::CtxKilled(kind) => {
                            let _ = ctx.kill(analyzer, *loc, kind);
                        }
                        ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                            let mut new_var =
                                analyzer.advance_var_in_ctx(cvar.into(), *loc, ctx).unwrap();
                            let res = new_var.sol_delete_range(analyzer).into_expr_err(*loc);
                            let _ = analyzer.add_if_err(res);
                        }
                        ExprRet::Multi(inner) => {
                            inner
                                .iter()
                                .for_each(|i| delete_match(ctx, loc, analyzer, i.clone()));
                        }
                        ExprRet::Null => {}
                    }
                }

                self.parse_ctx_expr(expr, ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    tracing::trace!("Delete variable pop");
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(
                            loc,
                            "Delete operation had no right hand side".to_string(),
                        ));
                    };

                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    delete_match(ctx, &loc, analyzer, ret);
                    Ok(())
                })
            }

            // de/increment stuff
            PreIncrement(loc, expr) => self.pre_increment(expr, *loc, ctx),
            PostIncrement(loc, expr) => self.post_increment(expr, *loc, ctx),
            PreDecrement(loc, expr) => self.pre_decrement(expr, *loc, ctx),
            PostDecrement(loc, expr) => self.post_decrement(expr, *loc, ctx),

            // Misc.
            Variable(ident) => self.variable(ident, ctx, None),
            Type(loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        ctx.push_expr(ExprRet::Single(*idx), self)
                            .into_expr_err(*loc)?;
                        Ok(())
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        ctx.push_expr(ExprRet::Single(idx), self)
                            .into_expr_err(*loc)?;
                        Ok(())
                    }
                } else {
                    ctx.push_expr(ExprRet::Null, self).into_expr_err(*loc)?;
                    Ok(())
                }
            }
            Parenthesis(_loc, expr) => self.parse_ctx_expr(expr, ctx),
        }
    }
}
