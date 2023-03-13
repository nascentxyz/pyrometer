use shared::analyzer::AsDotStr;
use shared::analyzer::GraphLike;
use shared::context::*;

use shared::range::elem_ty::Dynamic;

use shared::range::Range;
use shared::range::{elem_ty::Elem, SolcRange};
use solang_parser::pt::StorageLocation;
use solang_parser::pt::VariableDeclaration;

use crate::VarType;
use petgraph::{visit::EdgeRef, Direction};
use shared::{analyzer::AnalyzerLike, nodes::*, range::elem::RangeOp, Edge, Node, NodeIdx};
use solang_parser::pt::{Expression, Loc, Statement};

pub mod exprs;
use exprs::*;

pub mod analyzers;
pub mod queries;

#[derive(Debug, Clone)]
pub enum ExprRet {
    CtxKilled,
    Single((ContextNode, NodeIdx)),
    SingleLiteral((ContextNode, NodeIdx)),
    Multi(Vec<ExprRet>),
    Fork(Box<ExprRet>, Box<ExprRet>),
}

impl ExprRet {
    pub fn expect_single(&self) -> (ContextNode, NodeIdx) {
        match self {
            ExprRet::Single(inner) => *inner,
            ExprRet::SingleLiteral(inner) => *inner,
            ExprRet::Multi(inner) if inner.len() == 1 => inner[0].expect_single(),
            e => panic!("Expected a single return got: {e:?}"),
        }
    }

    pub fn is_single(&self) -> bool {
        matches!(self, ExprRet::Single(_))
    }

    pub fn has_fork(&self) -> bool {
        match self {
            ExprRet::Fork(_, _) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_fork()),
            _ => false,
        }
    }

    pub fn expect_multi(self) -> Vec<ExprRet> {
        match self {
            ExprRet::Multi(inner) => inner,
            _ => panic!("Expected a multi return got single"),
        }
    }

    pub fn try_as_func_input_str(&self, analyzer: &(impl GraphLike + AnalyzerLike)) -> String {
        match self {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => {
                let (_, idx) = inner;
                let var_ty = VarType::try_from_idx(analyzer, *idx).expect("Non-typeable as type");
                var_ty.as_dot_str(analyzer)
            }
            ExprRet::Multi(inner) if !self.has_fork() => {
                let mut strs = vec![];
                for ret in inner.iter() {
                    strs.push(ret.try_as_func_input_str(analyzer));
                }
                format!("({})", strs.join(", "))
            }
            _ => todo!("here"),
        }
    }

    pub fn as_flat_vec(&self) -> Vec<NodeIdx> {
        let mut idxs = vec![];
        match self {
            ExprRet::Single((_, idx)) | ExprRet::SingleLiteral((_, idx)) => idxs.push(*idx),
            ExprRet::Multi(inner) => {
                idxs.extend(
                    inner
                        .iter()
                        .map(|expr| expr.expect_single().1)
                        .collect::<Vec<_>>(),
                );
            }
            _ => {}
        }
        idxs
    }
}

impl<T> ContextBuilder for T where T: AnalyzerLike<Expr = Expression> + Sized + ExprParser {}

pub trait ContextBuilder: AnalyzerLike<Expr = Expression> + Sized + ExprParser {
    fn parse_ctx_statement(
        &mut self,
        stmt: &Statement,
        unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        if let Some(parent) = parent_ctx {
            match self.node(parent) {
                Node::Context(_) => {
                    let ctx = ContextNode::from(parent.into());
                    if ctx.is_ended(self) {
                        return;
                    }
                    if ctx.live_forks(self).is_empty() {
                        self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
                    } else {
                        ctx.live_forks(self).iter().for_each(|fork_ctx| {
                            self.parse_ctx_stmt_inner(stmt, unchecked, Some(*fork_ctx));
                        });
                    }
                }
                _ => self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx),
            }
        } else {
            self.parse_ctx_stmt_inner(stmt, unchecked, parent_ctx)
        }
    }

    fn parse_ctx_stmt_inner(
        &mut self,
        stmt: &Statement,
        _unchecked: bool,
        parent_ctx: Option<impl Into<NodeIdx> + Clone + Copy>,
    ) where
        Self: Sized,
    {
        use Statement::*;
        // println!("stmt: {:?}", stmt);
        match stmt {
            Block {
                loc,
                unchecked,
                statements,
            } => {
                let parent = parent_ctx.expect("Free floating contexts shouldn't happen");
                let ctx_node = match self.node(parent) {
                    Node::Function(_fn_node) => {
                        let ctx = Context::new(
                            FunctionNode::from(parent.into()),
                            FunctionNode::from(parent.into()).name(self),
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
                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionParam)
                    .map(|edge| FunctionParamNode::from(edge.source()))
                    .collect::<Vec<FunctionParamNode>>()
                    .iter()
                    .for_each(|param_node| {
                        let func_param = param_node.underlying(self);
                        if let Some(cvar) =
                            ContextVar::maybe_new_from_func_param(self, func_param.clone())
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                self.graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionReturn)
                    .map(|edge| FunctionReturnNode::from(edge.source()))
                    .collect::<Vec<FunctionReturnNode>>()
                    .iter()
                    .for_each(|ret_node| {
                        let func_ret = ret_node.underlying(self);
                        if let Some(cvar) =
                            ContextVar::maybe_new_from_func_ret(self, func_ret.clone())
                        {
                            let cvar_node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(
                                cvar_node,
                                ctx_node,
                                Edge::Context(ContextEdge::Variable),
                            );
                        }
                    });

                let forks = ContextNode::from(ctx_node).live_forks(self);
                if forks.is_empty() {
                    statements.iter().for_each(|stmt| {
                        self.parse_ctx_statement(stmt, *unchecked, Some(ctx_node))
                    });
                } else {
                    forks.into_iter().for_each(|fork| {
                        statements.iter().for_each(|stmt| {
                            self.parse_ctx_statement(stmt, *unchecked, Some(fork))
                        });
                    });
                }
            }
            VariableDefinition(loc, var_decl, maybe_expr) => {
                let ctx = ContextNode::from(
                    parent_ctx
                        .expect("No context for variable definition?")
                        .into(),
                );
                let forks = ctx.live_forks(self);
                if forks.is_empty() {
                    let lhs_paths = self.parse_ctx_expr(&var_decl.ty, ctx);
                    if let Some(rhs) = maybe_expr {
                        let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                        self.match_var_def(var_decl, *loc, &lhs_paths, Some(&rhs_paths));
                    } else {
                        self.match_var_def(var_decl, *loc, &lhs_paths, None)
                    }
                } else {
                    forks.into_iter().for_each(|ctx| {
                        let lhs_paths = self.parse_ctx_expr(&var_decl.ty, ctx);
                        if let Some(rhs) = maybe_expr {
                            let rhs_paths = self.parse_ctx_expr(rhs, ctx);
                            self.match_var_def(var_decl, *loc, &lhs_paths, Some(&rhs_paths));
                        } else {
                            self.match_var_def(var_decl, *loc, &lhs_paths, None)
                        }
                    });
                }
            }
            Args(_loc, _args) => {}
            If(loc, if_expr, true_expr, maybe_false_expr) => {
                let ctx = ContextNode::from(parent_ctx.expect("Dangling if statement").into());
                let forks = ctx.live_forks(self);
                if forks.is_empty() {
                    self.cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, ctx)
                } else {
                    forks.into_iter().for_each(|parent| {
                        self.cond_op_stmt(*loc, if_expr, true_expr, maybe_false_expr, parent)
                    })
                }
            }
            While(_loc, _cond, _body) => {
                todo!("while")
            }
            Expression(_loc, expr) => {
                if let Some(parent) = parent_ctx {
                    let _paths = self.parse_ctx_expr(expr, ContextNode::from(parent.into()));
                }
            }
            For(_loc, _maybe_for_start, _maybe_for_middle, _maybe_for_end, _maybe_for_body) => {
                todo!("for");
            }
            DoWhile(_loc, _while_stmt, _while_expr) => {
                todo!("do while");
            }
            Continue(_loc) => {
                todo!("continue")
            }
            Break(_loc) => {
                todo!("break")
            }
            Assembly {
                loc: _,
                dialect: _,
                flags: _,
                block: _yul_block,
            } => {
                todo!("assembly not supported")
            }
            Return(loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let forks = ContextNode::from(parent.into()).live_forks(self);
                        if forks.is_empty() {
                            let paths =
                                self.parse_ctx_expr(ret_expr, ContextNode::from(parent.into()));
                            self.return_match(loc, &paths);
                        } else {
                            forks.into_iter().for_each(|parent| {
                                let paths = self.parse_ctx_expr(ret_expr, parent);
                                self.return_match(loc, &paths);
                                // match paths {
                                //     ExprRet::CtxKilled => {}
                                //     ExprRet::Single((ctx, expr)) => {
                                //         self.add_edge(
                                //             expr,
                                //             ctx,
                                //             Edge::Context(ContextEdge::Return),
                                //         );
                                //         // self.add_edge(expr, ctx, Edge::Context(ContextEdge::Variable));
                                //         ctx.add_return_node(*loc, expr.into(), self);
                                //     }
                                //     ExprRet::Multi(rets) => {
                                //         rets.into_iter().for_each(|expr_ret| {
                                //             let (ctx, expr) = expr_ret.expect_single();
                                //             self.add_edge(
                                //                 expr,
                                //                 ctx,
                                //                 Edge::Context(ContextEdge::Return),
                                //             );
                                //             // self.add_edge(expr, ctx, Edge::Context(ContextEdge::Variable));
                                //             ctx.add_return_node(*loc, expr.into(), self);
                                //         });
                                //     }
                                //     ExprRet::Fork(_world1, _world2) => {
                                //         todo!("here")
                                //     }
                                // }
                            });
                        }
                    }
                }
            }
            Revert(loc, _maybe_err_path, _exprs) => {
                if let Some(parent) = parent_ctx {
                    let parent = ContextNode::from(parent.into());
                    let forks = parent.live_forks(self);
                    if forks.is_empty() {
                        parent.kill(self, *loc);
                    } else {
                        forks.into_iter().for_each(|parent| {
                            parent.kill(self, *loc);
                        });
                    }
                }
            }
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {}
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }

    fn return_match(&mut self, loc: &Loc, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) | ExprRet::SingleLiteral((ctx, expr)) => {
                self.add_edge(*expr, *ctx, Edge::Context(ContextEdge::Return));
                ctx.add_return_node(*loc, ContextVarNode(expr.index()), self);
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    let (ctx, expr) = expr_ret.expect_single();
                    self.add_edge(expr, ctx, Edge::Context(ContextEdge::Return));
                    // self.add_edge(expr, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_return_node(*loc, expr.into(), self);
                });
            }
            ExprRet::Fork(world1, world2) => {
                self.return_match(loc, world1);
                self.return_match(loc, world2);
            }
        }
    }

    fn match_var_def(
        &mut self,
        var_decl: &VariableDeclaration,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: Option<&ExprRet>,
    ) {
        match (lhs_paths, rhs_paths) {
            (ExprRet::CtxKilled, _) => {},
            (_, Some(ExprRet::CtxKilled)) => {},
            (ExprRet::Single((_lhs_ctx, ty)), Some(ExprRet::SingleLiteral((rhs_ctx, rhs)))) => {
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                rhs_cvar.cast_from_ty(ty, self);
                self.match_var_def(
                    var_decl,
                    loc,
                    lhs_paths,
                    Some(&ExprRet::Single((*rhs_ctx, rhs_cvar.into()))),
                )
            }
            (ExprRet::Single((_lhs_ctx, ty)), Some(ExprRet::Single((rhs_ctx, rhs)))) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                // if let VarType::Array(_, ref mut range) = ty {
                //     *range = Some(self.tmp_length(ContextVarNode::from(*rhs), *rhs_ctx, loc))
                // }

                // if ty.is_dyn_builtin(self) {
                //     if let Some(r) = ContextVarNode::from(ty).range(self) {
                //         let mut min = r.range_min().clone();
                //         let mut max = r.range_max().clone();

                //         if let Some(rd) = min.maybe_range_dyn() {
                //             rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                //             next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                //         }

                //         if let Some(rd) = max.maybe_range_dyn() {
                //             rd.len = Elem::Dynamic(Dynamic::new(len_node, loc));
                //             next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                //         }
                //     }
                // }

                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.clone(),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                self.add_edge(lhs, *rhs_ctx, Edge::Context(ContextEdge::Variable));
                let rhs = ContextVarNode::from(*rhs);
                let (_, new_lhs) = self.assign(loc, lhs, rhs, *rhs_ctx).expect_single();
                self.add_edge(new_lhs, *rhs_ctx, Edge::Context(ContextEdge::Variable));
            }
            (ExprRet::Single((lhs_ctx, ty)), None) => {
                let name = var_decl.name.clone().expect("Variable wasn't named");
                let ty = VarType::try_from_idx(self, *ty).expect("Not a known type");
                let var = ContextVar {
                    loc: Some(loc),
                    name: name.to_string(),
                    display_name: name.to_string(),
                    storage: var_decl.storage.clone(),
                    is_tmp: false,
                    is_symbolic: true,
                    tmp_of: None,
                    ty,
                };
                let lhs = ContextVarNode::from(self.add_node(Node::ContextVar(var)));
                self.add_edge(lhs, *lhs_ctx, Edge::Context(ContextEdge::Variable));
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), Some(ExprRet::Multi(rhs_sides))) => {
                rhs_sides.iter().for_each(|expr_ret| {
                    self.match_var_def(var_decl, loc, l, Some(expr_ret));
                });
            }
            (ExprRet::Multi(lhs_sides), r @ Some(ExprRet::Single(_))) => {
                lhs_sides.iter().for_each(|expr_ret| {
                    self.match_var_def(var_decl, loc, expr_ret, r);
                });
            }
            (ExprRet::Multi(lhs_sides), None) => {
                lhs_sides.iter().for_each(|expr_ret| {
                    self.match_var_def(var_decl, loc, expr_ret, None);
                });
            }
            (ExprRet::Multi(lhs_sides), Some(ExprRet::Multi(rhs_sides))) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    lhs_sides.iter().zip(rhs_sides.iter()).for_each(
                        |(lhs_expr_ret, rhs_expr_ret)| {
                            self.match_var_def(var_decl, loc, lhs_expr_ret, Some(rhs_expr_ret))
                        },
                    );
                } else {
                    rhs_sides.iter().for_each(|rhs_expr_ret| {
                        self.match_var_def(var_decl, loc, lhs_paths, Some(rhs_expr_ret))
                    });
                }
            }
            (
                ExprRet::Fork(lhs_world1, lhs_world2),
                Some(ExprRet::Fork(rhs_world1, rhs_world2)),
            ) => {
                self.match_var_def(var_decl, loc, lhs_world1, Some(rhs_world1));
                self.match_var_def(var_decl, loc, lhs_world1, Some(rhs_world2));

                self.match_var_def(var_decl, loc, lhs_world2, Some(rhs_world1));
                self.match_var_def(var_decl, loc, lhs_world2, Some(rhs_world2))
            }
            (l @ ExprRet::Single(_), Some(ExprRet::Fork(world1, world2))) => {
                self.match_var_def(var_decl, loc, l, Some(world1));
                self.match_var_def(var_decl, loc, l, Some(world2));
            }
            (m @ ExprRet::Multi(_), Some(ExprRet::Fork(world1, world2))) => {
                self.match_var_def(var_decl, loc, m, Some(world1));
                self.match_var_def(var_decl, loc, m, Some(world2));
            }
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    fn match_expr(&mut self, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) | ExprRet::SingleLiteral((ctx, expr)) => {
                self.add_edge(*expr, *ctx, Edge::Context(ContextEdge::Call));
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    self.match_expr(expr_ret);
                });
            }
            ExprRet::Fork(world1, world2) => {
                self.match_expr(world1);
                self.match_expr(world2);
            }
        }
    }

    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> ExprRet {
        if ctx.is_ended(self) {
            return ExprRet::CtxKilled;
        }

        if ctx.live_forks(self).is_empty() {
            self.parse_ctx_expr_inner(expr, ctx)
        } else {
            let rets: Vec<_> = ctx
                .live_forks(self)
                .iter()
                .map(|fork_ctx| self.parse_ctx_expr(expr, *fork_ctx))
                .collect();
            if rets.len() == 1 {
                rets.into_iter().take(1).next().unwrap()
            } else {
                ExprRet::Multi(rets)
            }
        }
    }

    fn parse_ctx_expr_inner(&mut self, expr: &Expression, ctx: ContextNode) -> ExprRet {
        use Expression::*;
        // println!("ctx: {}, {:?}", ctx.underlying(self).path, expr);
        match expr {
            // literals
            NumberLiteral(loc, int, exp) => self.number_literal(ctx, *loc, int, exp, false),
            AddressLiteral(loc, addr) => self.address_literal(ctx, *loc, addr),
            StringLiteral(lits) => ExprRet::Multi(
                lits.iter()
                    .map(|lit| self.string_literal(ctx, lit.loc, &lit.string))
                    .collect(),
            ),
            BoolLiteral(loc, b) => self.bool_literal(ctx, *loc, *b),
            HexNumberLiteral(loc, b) => self.hex_num_literal(ctx, *loc, b, false),
            HexLiteral(hexes) => self.hex_literals(ctx, hexes),
            RationalNumberLiteral(_, _, _, _) => todo!("Rational literal"),
            UnaryMinus(_loc, expr) => match &**expr {
                NumberLiteral(loc, int, exp) => self.number_literal(ctx, *loc, int, exp, true),
                HexNumberLiteral(loc, b) => self.hex_num_literal(ctx, *loc, b, true),
                e => todo!("UnaryMinus unexpected rhs: {e:?}"),
            },
            UnaryPlus(_loc, e) => todo!("UnaryPlus unexpected rhs: {e:?}"),

            // Binary ops
            Power(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Exp, false)
            }
            Add(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Add, false)
            }
            AssignAdd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Add, true)
            }
            Subtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Sub, false)
            }
            AssignSubtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Sub, true)
            }
            Multiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mul, false)
            }
            AssignMultiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Mul, true)
            }
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div, false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, RangeOp::Div, true)
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
            Complement(_loc, _expr) => todo!("Complement"),

            // assign
            Assign(loc, lhs_expr, rhs_expr) => self.assign_exprs(*loc, lhs_expr, rhs_expr, ctx),
            List(loc, params) => self.list(ctx, *loc, params),
            // array
            ArraySubscript(_loc, ty_expr, None) => self.array_ty(ty_expr, ctx),
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                self.index_into_array(*loc, ty_expr, index_expr, ctx)
            }
            ArraySlice(_loc, _lhs_expr, _maybe_middle_expr, _maybe_rhs) => todo!("Array slice"),
            ArrayLiteral(_, _) => todo!("Array literal"),

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
            FunctionCallBlock(_loc, _func_expr, _input_exprs) => todo!("Function call block"),
            NamedFunctionCall(_loc, _func_expr, _input_exprs) => todo!("Named function call"),
            FunctionCall(loc, func_expr, input_exprs) => {
                match &**func_expr {
                    Variable(ident) => {
                        // It is a function call, check if we have the ident in scope
                        let funcs = ctx.visible_funcs(self);
                        // filter down all funcs to those that match
                        let possible_funcs = funcs
                            .iter()
                            .filter(|func| func.name(self).starts_with(&format!("{}(", ident.name)))
                            .collect::<Vec<_>>();

                        if possible_funcs.is_empty() {
                            // this is a builtin, cast, or unknown function?
                            let (func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                                ExprRet::Single((ctx, idx)) => (ctx, idx),
                                m @ ExprRet::Multi(_) => m.expect_single(),
                                ExprRet::CtxKilled => return ExprRet::CtxKilled,
                                e => todo!("got fork in func call: {:?}", e),
                            };
                            self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
                        } else if possible_funcs.len() == 1 {
                            let inputs = ExprRet::Multi(
                                input_exprs
                                    .iter()
                                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                                    .collect(),
                            );
                            self.setup_fn_call(
                                &ident.loc,
                                &inputs,
                                (*possible_funcs[0]).into(),
                                ctx,
                            )
                        } else {
                            // this is the annoying case due to function overloading & type inference on number literals
                            let lits = input_exprs
                                .iter()
                                .map(|expr| {
                                    match expr {
                                        UnaryMinus(_, expr) => {
                                            // negative number potentially
                                            matches!(**expr, NumberLiteral(..) | HexLiteral(..))
                                        }
                                        NumberLiteral(..) | HexLiteral(..) => true,
                                        _ => false,
                                    }
                                })
                                .collect();
                            let inputs = ExprRet::Multi(
                                input_exprs
                                    .iter()
                                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                                    .collect(),
                            );

                            if let Some(func) = self.disambiguate_fn_call(
                                &ident.name,
                                lits,
                                &inputs,
                                &possible_funcs,
                            ) {
                                self.setup_fn_call(loc, &inputs, func.into(), ctx)
                            } else {
                                ExprRet::CtxKilled
                            }
                        }
                    }
                    _ => {
                        let (func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                            ExprRet::Single((ctx, idx)) => (ctx, idx),
                            m @ ExprRet::Multi(_) => m.expect_single(),
                            ExprRet::CtxKilled => return ExprRet::CtxKilled,
                            e => todo!("got fork in func call: {:?}", e),
                        };
                        self.intrinsic_func_call(loc, input_exprs, func_idx, func_ctx)
                    }
                }
            }
            // member
            New(_loc, expr) => self.parse_ctx_expr(expr, ctx),
            This(loc) => {
                let var = ContextVar::new_from_contract(*loc, ctx.associated_contract(self), self);
                let cvar = self.add_node(Node::ContextVar(var));
                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                ExprRet::Single((ctx, cvar))
            }
            MemberAccess(loc, member_expr, ident) => {
                self.member_access(*loc, member_expr, ident, ctx)
            }

            Delete(_loc, _expr) => todo!("Delete"),

            // de/increment stuff
            PreIncrement(_loc, _expr) => todo!("Preincrement"),
            PostIncrement(_loc, _expr) => todo!("Post increment"),
            PreDecrement(_loc, _expr) => todo!("Predecrement"),
            PostDecrement(_loc, _expr) => todo!("Post decrement"),

            // Misc.
            Variable(ident) => self.variable(ident, ctx),
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        ExprRet::Single((ctx, *idx))
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        ExprRet::Single((ctx, idx))
                    }
                } else {
                    todo!("??")
                }
            }
            Parenthesis(_loc, expr) => self.parse_ctx_expr(expr, ctx),
            Unit(_, _, _) => todo!("Unit"),
        }
    }

    fn disambiguate_fn_call(
        &mut self,
        fn_name: &str,
        literals: Vec<bool>,
        input_paths: &ExprRet,
        funcs: &[&FunctionNode],
    ) -> Option<FunctionNode> {
        // try to find the function based on naive signature
        // This doesnt do type inference on NumberLiterals (i.e. 100 could be uintX or intX, and there could
        // be a function that takes an int256 but we evaled as uint256)
        let fn_sig = format!("{}{}", fn_name, input_paths.try_as_func_input_str(self));
        if let Some(func) = funcs.iter().find(|func| func.name(self) == fn_sig) {
            return Some(**func);
        }

        // filter by input len
        let inputs = input_paths.as_flat_vec();
        let funcs: Vec<&&FunctionNode> = funcs
            .iter()
            .filter(|func| func.params(self).len() == inputs.len())
            .collect();

        if funcs.len() == 1 {
            return Some(**funcs[0]);
        }

        if !literals.iter().any(|i| *i) {
            None
        } else {
            // println!("funcs: {:?}", funcs);
            let funcs = funcs
                .iter()
                .filter(|func| {
                    let params = func.params(self);
                    params
                        .iter()
                        .zip(&inputs)
                        .enumerate()
                        .all(|(i, (param, input))| {
                            if param.as_dot_str(self)
                                == ContextVarNode::from(*input).as_dot_str(self)
                            {
                                true
                            } else if literals[i] {
                                let as_concrete = ContextVarNode::from(*input).as_concrete(self);
                                let possibilities = as_concrete.possible_builtins_from_ty_inf();
                                let param_ty = param.ty(self);
                                match self.node(param_ty) {
                                    Node::Builtin(b) => possibilities.contains(b),
                                    _ => false,
                                }
                            } else {
                                false
                            }
                        })
                })
                .collect::<Vec<_>>();
            if funcs.len() == 1 {
                Some(***funcs[0])
            } else {
                // this would be invalid solidity, likely the user needs to perform a cast
                None
            }
        }
    }

    fn setup_fn_call(
        &mut self,
        loc: &Loc,
        inputs: &ExprRet,
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> ExprRet {

        // println!("func: {:#?}", FunctionNode::from(func_idx).underlying(self));
        // if we have a single match thats our function
        let mut var = match ContextVar::maybe_from_user_ty(self, *loc, func_idx) {
            Some(v) => v,
            None => panic!(
                "Could not create context variable from user type: {:?}",
                self.node(func_idx)
            ),
        };
        if let Some(r) = var.fallback_range(self) {
            if var.storage.is_some() {
                if let Elem::Concrete(c) = r.range_max() {
                    if let Some(size) = c.val.int_size() {
                        var.set_range_max(Elem::from(Concrete::Uint(size, 0.into())), None)
                    }
                }
            }
        }
        let new_cvarnode = self.add_node(Node::ContextVar(var));
        self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
        if let Some(func_node) = ContextVarNode::from(new_cvarnode).ty(self).func_node(self) {
            self.func_call(ctx, *loc, inputs, func_node)
        } else {
            unreachable!()
        }
    }

    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> ExprRet {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        "require" | "assert" => {
                            self.handle_require(input_exprs, ctx);
                            ExprRet::Multi(vec![])
                        }
                        "type" => ExprRet::Single(
                            self.parse_ctx_expr(&input_exprs[0], ctx).expect_single(),
                        ),
                        "ecrecover" => {
                            input_exprs.iter().for_each(|expr| {
                                // we want to parse even though we dont need the variables here
                                let _ = self.parse_ctx_expr(expr, ctx);
                            });
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Address).into(),
                                self,
                            );
                            let cvar = self.add_node(Node::ContextVar(var));
                            ExprRet::Single((ctx, cvar))
                        }
                        e => todo!("builtin function: {:?}", e),
                    }
                } else {
                    panic!("unnamed builtin?")
                }
            }
            Node::Builtin(Builtin::Array(_)) => {
                // create a new list
                let (ctx, len_cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                let ty = VarType::try_from_idx(self, func_idx);

                let new_arr = ContextVar {
                    loc: Some(*loc),
                    name: format!("tmp_arr{}", ctx.new_tmp(self)),
                    display_name: "arr".to_string(),
                    storage: None,
                    is_tmp: true,
                    is_symbolic: false,
                    tmp_of: None,
                    ty: ty.expect("No type for node"),
                };

                let arr = ContextVarNode::from(self.add_node(Node::ContextVar(new_arr)));

                let len_var = ContextVar {
                    loc: Some(*loc),
                    name: arr.name(self) + ".length",
                    display_name: arr.display_name(self) + ".length",
                    storage: None,
                    is_tmp: true,
                    tmp_of: None,
                    is_symbolic: true,
                    ty: ContextVarNode::from(len_cvar).underlying(self).ty.clone(),
                };

                let len_cvar = self.add_node(Node::ContextVar(len_var));
                self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, arr, Edge::Context(ContextEdge::AttrAccess));

                // update the length
                if let Some(r) = arr.range(self) {
                    let min = r.evaled_range_min(self);
                    let max = r.evaled_range_max(self);

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }

                ExprRet::Single((ctx, arr.into()))
            }
            Node::Builtin(ty) => {
                // it is a cast
                let ty = ty.clone();
                let (ctx, cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();

                let new_var = ContextVarNode::from(cvar).as_cast_tmp(*loc, ctx, ty.clone(), self);

                new_var.underlying_mut(self).ty = VarType::try_from_idx(self, func_idx).expect("");

                // cast the ranges
                if let Some(r) = ContextVarNode::from(cvar).range(self) {
                    let curr_range = SolcRange::try_from_builtin(&ty).expect("No default range");
                    new_var.set_range_min(self, r.range_min().cast(curr_range.range_min()));
                    new_var.set_range_max(self, r.range_max().cast(curr_range.range_max()));
                    // cast the range exclusions - TODO: verify this is correct
                    let mut exclusions = r.range_exclusions();
                    exclusions.iter_mut().for_each(|range| {
                        *range = range.clone().cast(curr_range.range_min());
                    });
                    new_var.set_range_exclusions(self, exclusions);
                } else {
                    // todo!("unable to cast: {:?}, {ty:?}", self.node(cvar))
                }
                ExprRet::Single((ctx, new_var.into()))
            }
            Node::ContextVar(_c) => {
                // its a user type
                // TODO: figure out if we actually need to do anything?
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            Node::Contract(_) => {
                // TODO: figure out if we need to do anything
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            e => todo!("{:?}", e),
        }
    }

    fn func_call(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        input_paths: &ExprRet,
        func: FunctionNode,
    ) -> ExprRet {
        let params = func.params(self);
        match input_paths {
            ExprRet::Single((_ctx, input_var)) => {
                // if we get a single var, we expect the func to only take a single
                // variable
                return self.func_call_inner(
                    ctx,
                    func,
                    loc,
                    vec![ContextVarNode::from(*input_var).latest_version(self)],
                    params,
                );
            }
            ExprRet::Multi(inputs) => {
                // check if the inputs length matchs func params length
                // if they do, check that none are forks
                if inputs.len() == params.len() {
                    if !input_paths.has_fork() {
                        let input_vars = inputs
                            .iter()
                            .map(|expr_ret| {
                                let (_ctx, var) = expr_ret.expect_single();
                                ContextVarNode::from(var).latest_version(self)
                            })
                            .collect();
                        return self.func_call_inner(ctx, func, loc, input_vars, params);
                    } else {
                        panic!("input has fork - need to flatten")
                    }
                }
            }
            _ => todo!("here"),
        }
        ExprRet::CtxKilled
    }

    fn func_call_inner(
        &mut self,
        ctx: ContextNode,
        func_node: FunctionNode,
        loc: Loc,
        inputs: Vec<ContextVarNode>,
        params: Vec<FunctionParamNode>,
    ) -> ExprRet {
        let fn_ext = ctx.is_fn_ext(func_node, self);

        let subctx = ContextNode::from(self.add_node(Node::Context(Context::new_subctx(
            ctx,
            loc,
            false,
            Some(func_node),
            fn_ext,
            self,
        ))));
        ctx.add_child(subctx, self);
        let ctx_fork = self.add_node(Node::FunctionCall);
        self.add_edge(ctx_fork, ctx, Edge::Context(ContextEdge::Subcontext));
        self.add_edge(ctx_fork, func_node, Edge::Context(ContextEdge::Call));
        self.add_edge(
            NodeIdx::from(subctx.0),
            ctx_fork,
            Edge::Context(ContextEdge::Subcontext),
        );

        params.iter().zip(inputs.iter()).for_each(|(param, input)| {
            if let Some(name) = param.maybe_name(self) {
                let mut new_cvar = input.latest_version(self).underlying(self).clone();
                new_cvar.loc = Some(param.loc(self));
                new_cvar.name = name.clone();
                new_cvar.display_name = name;
                new_cvar.is_tmp = false;
                new_cvar.storage =
                    if let Some(StorageLocation::Storage(_)) = param.underlying(self).storage {
                        new_cvar.storage
                    } else {
                        None
                    };

                if let Some(param_ty) = VarType::try_from_idx(self, param.ty(self)) {
                    let ty = new_cvar.ty.clone();
                    if !ty.ty_eq(&param_ty, self) {
                        if let Some(new_ty) = ty.try_cast(&param_ty, self) {
                            new_cvar.ty = new_ty;
                        }
                    }
                }

                let node = ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                if let (Some(r), Some(r2)) = (node.range(self), param.range(self)) {
                    let new_min = r.range_min().cast(r2.range_min());
                    let new_max = r.range_max().cast(r2.range_max());
                    node.try_set_range_min(self, new_min);
                    node.try_set_range_max(self, new_max);
                    node.try_set_range_exclusions(self, r.exclusions);
                }
                self.add_edge(node, subctx, Edge::Context(ContextEdge::Variable));
            }
        });

        if let Some(body) = func_node.underlying(self).body.clone() {
            // add return nodes into the subctx
            func_node.returns(self).iter().for_each(|ret| {
                if let Some(var) =
                    ContextVar::maybe_new_from_func_ret(self, ret.underlying(self).clone())
                {
                    let cvar = self.add_node(Node::ContextVar(var));
                    self.add_edge(cvar, subctx, Edge::Context(ContextEdge::Variable));
                }
            });
            self.parse_ctx_statement(&body, false, Some(subctx));
            // adjust any storage variables
            let vars = subctx.vars(self);
            vars.iter().for_each(|old_var| {
                let var = old_var.latest_version(self);
                let underlying = var.underlying(self).clone();
                if underlying.storage.is_some() {
                    if let Some(parent_var) = ctx.var_by_name(self, &underlying.name) {
                        let parent_var = parent_var.latest_version(self);
                        if let Some(r) = underlying.ty.range(self) {
                            let new_parent_var = self.advance_var_in_ctx(
                                parent_var,
                                underlying.loc.expect("No loc for val change"),
                                ctx,
                            );
                            new_parent_var.set_range_min(self, r.range_min());
                            new_parent_var.set_range_max(self, r.range_max());
                            new_parent_var.set_range_exclusions(self, r.range_exclusions());
                        }
                    } else {
                        todo!("storage was some, but not in parent: {}", underlying.name);
                    }
                }
            });
            // adjust the output type to match the return type of the function call
            ExprRet::Multi(
                subctx
                    .underlying(self)
                    .ret
                    .clone()
                    .into_iter()
                    .map(|(_, node)| ExprRet::Single((ctx, node.into())))
                    .collect(),
            )
        } else {
            ExprRet::Multi(
                func_node
                    .returns(self)
                    .iter()
                    .filter_map(|ret| {
                        let underlying = ret.underlying(self);
                        let var = ContextVar::maybe_new_from_func_ret(self, underlying.clone())?;
                        let node = self.add_node(Node::ContextVar(var));
                        Some(ExprRet::Single((ctx, node)))
                    })
                    .collect(),
            )
        }
    }

    fn assign_exprs(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> ExprRet {
        let lhs_paths = self.parse_ctx_expr(lhs_expr, ctx);
        let rhs_paths = self.parse_ctx_expr(rhs_expr, ctx);
        self.match_assign_sides(loc, &lhs_paths, &rhs_paths)
    }

    fn match_assign_sides(
        &mut self,
        loc: Loc,
        lhs_paths: &ExprRet,
        rhs_paths: &ExprRet,
    ) -> ExprRet {
        match (lhs_paths, rhs_paths) {
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                rhs_cvar.cast_from(&lhs_cvar, self);
                println!(
                    "HERE {:?}, {:?}",
                    self.node(NodeIdx::from(rhs_cvar.0)),
                    rhs_cvar.range(self)
                );
                self.assign(loc, lhs_cvar, rhs_cvar, *rhs_ctx)
            }
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::Single((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                self.assign(loc, lhs_cvar, rhs_cvar, *rhs_ctx)
            }
            (l @ ExprRet::Single((_lhs_ctx, _lhs)), ExprRet::Multi(rhs_sides)) => ExprRet::Multi(
                rhs_sides
                    .iter()
                    .map(|expr_ret| self.match_assign_sides(loc, l, expr_ret))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), r @ ExprRet::Single(_)) => ExprRet::Multi(
                lhs_sides
                    .iter()
                    .map(|expr_ret| self.match_assign_sides(loc, expr_ret, r))
                    .collect(),
            ),
            (ExprRet::Multi(lhs_sides), ExprRet::Multi(rhs_sides)) => {
                // try to zip sides if they are the same length
                if lhs_sides.len() == rhs_sides.len() {
                    ExprRet::Multi(
                        lhs_sides
                            .iter()
                            .zip(rhs_sides.iter())
                            .map(|(lhs_expr_ret, rhs_expr_ret)| {
                                self.match_assign_sides(loc, lhs_expr_ret, rhs_expr_ret)
                            })
                            .collect(),
                    )
                } else {
                    ExprRet::Multi(
                        rhs_sides
                            .iter()
                            .map(|rhs_expr_ret| {
                                self.match_assign_sides(loc, lhs_paths, rhs_expr_ret)
                            })
                            .collect(),
                    )
                }
            }
            (ExprRet::Fork(lhs_world1, lhs_world2), ExprRet::Fork(rhs_world1, rhs_world2)) => {
                ExprRet::Fork(
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world1)),
                        Box::new(self.match_assign_sides(loc, lhs_world1, rhs_world2)),
                    )),
                    Box::new(ExprRet::Fork(
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world1)),
                        Box::new(self.match_assign_sides(loc, lhs_world2, rhs_world2)),
                    )),
                )
            }
            (l @ ExprRet::Single(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, l, world1)),
                Box::new(self.match_assign_sides(loc, l, world2)),
            ),
            (m @ ExprRet::Multi(_), ExprRet::Fork(world1, world2)) => ExprRet::Fork(
                Box::new(self.match_assign_sides(loc, m, world1)),
                Box::new(self.match_assign_sides(loc, m, world2)),
            ),
            (e, f) => todo!("any: {:?} {:?}", e, f),
        }
    }

    fn assign(
        &mut self,
        loc: Loc,
        lhs_cvar: ContextVarNode,
        rhs_cvar: ContextVarNode,
        ctx: ContextNode,
    ) -> ExprRet {
        let (new_lower_bound, new_upper_bound): (Elem<Concrete>, Elem<Concrete>) = (
            Elem::Dynamic(Dynamic::new(rhs_cvar.latest_version(self).into(), loc)),
            Elem::Dynamic(Dynamic::new(rhs_cvar.latest_version(self).into(), loc)),
        );

        let new_lhs = self.advance_var_in_ctx(lhs_cvar.latest_version(self), loc, ctx);
        if !lhs_cvar.ty_eq(&rhs_cvar, self) {
            let _ = new_lhs.try_set_range_min(
                self,
                new_lower_bound.cast(lhs_cvar.range_min(self).expect("No range during cast?")),
            );
            let _ = new_lhs.try_set_range_max(
                self,
                new_upper_bound.cast(lhs_cvar.range_max(self).expect("No range during cast?")),
            );
        } else {
            let _ = new_lhs.try_set_range_min(self, new_lower_bound);
            let _ = new_lhs.try_set_range_max(self, new_upper_bound);
        }
        if let Some(rhs_range) = rhs_cvar.range(self) {
            new_lhs.try_set_range_exclusions(self, rhs_range.exclusions);
        }

        if let Some(arr) = lhs_cvar.index_to_array(self) {
            if let Some(index) = lhs_cvar.index_access_to_index(self) {
                let next_arr = self.advance_var_in_ctx(arr, loc, ctx);
                if next_arr.underlying(self).ty.is_dyn_builtin(self) {
                    if let Some(r) = next_arr.range(self) {
                        let min = r.evaled_range_min(self);
                        let max = r.evaled_range_max(self);

                        if let Some(mut rd) = min.maybe_range_dyn() {
                            rd.val.insert(
                                Elem::Dynamic(Dynamic::new(index.into(), loc)),
                                Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc)),
                            );
                            next_arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                        }

                        if let Some(mut rd) = max.maybe_range_dyn() {
                            rd.val.insert(
                                Elem::Dynamic(Dynamic::new(index.into(), loc)),
                                Elem::Dynamic(Dynamic::new(rhs_cvar.into(), loc)),
                            );
                            next_arr.set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                        }
                    }
                }
            }
        }

        ExprRet::Single((ctx, new_lhs.into()))
    }

    fn advance_var_in_ctx(
        &mut self,
        cvar_node: ContextVarNode,
        loc: Loc,
        ctx: ContextNode,
    ) -> ContextVarNode {
        assert_eq!(None, cvar_node.next_version(self));
        let mut new_cvar = cvar_node.latest_version(self).underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        if let Some(old_ctx) = cvar_node.maybe_ctx(self) {
            if old_ctx != ctx {
                self.add_edge(new_cvarnode, ctx, Edge::Context(ContextEdge::Variable));
            } else {
                self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
            }
        } else {
            self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        }

        ContextVarNode::from(new_cvarnode)
    }

    fn advance_var_underlying(&mut self, cvar_node: ContextVarNode, loc: Loc) -> &mut ContextVar {
        assert_eq!(None, cvar_node.next_version(self));
        let mut new_cvar = cvar_node.latest_version(self).underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode).underlying_mut(self)
    }
}
