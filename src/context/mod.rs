use ethers_core::types::U256;
use shared::analyzer::AsDotStr;
use shared::analyzer::GraphLike;
use shared::context::*;

use shared::range::elem_ty::Dynamic;

use shared::range::elem_ty::Elem;
use shared::range::Range;
use solang_parser::pt::VariableDeclaration;

use crate::VarType;
use petgraph::{visit::EdgeRef, Direction};
use shared::{analyzer::AnalyzerLike, nodes::*, range::elem::RangeOp, Edge, Node, NodeIdx};
use solang_parser::pt::{Expression, Loc, Statement};

pub mod func;
use func::*;

pub mod loops;
use loops::*;

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
            // println!("function entry: {:?}", parent_ctx.map(|ctx| self.node(ctx.into())));
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
                let mut entry_loc = None;
                let ctx_node = match self.node(parent) {
                    Node::Function(fn_node) => {
                        entry_loc = Some(fn_node.loc);
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
                let (params, inputs): (Vec<_>, Vec<_>) = self
                    .graph()
                    .edges_directed(parent.into(), Direction::Incoming)
                    .filter(|edge| *edge.weight() == Edge::FunctionParam)
                    .map(|edge| FunctionParamNode::from(edge.source()))
                    .collect::<Vec<FunctionParamNode>>()
                    .iter()
                    .filter_map(|param_node| {
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

                            Some((*param_node, ContextVarNode::from(cvar_node)))
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

                if let Some(fn_loc) = entry_loc {
                    self.func_call_inner(
                        true,
                        ctx_node.into(),
                        parent.into().into(),
                        fn_loc,
                        inputs,
                        params,
                        None,
                    );
                    return;
                }

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
            While(loc, cond, body) => {
                if let Some(parent) = parent_ctx {
                    self.while_loop(*loc, parent.into().into(), cond, body);
                }
            }
            Expression(_loc, expr) => {
                if let Some(parent) = parent_ctx {
                    let _paths = self.parse_ctx_expr(expr, ContextNode::from(parent.into()));
                }
            }
            For(loc, maybe_for_start, maybe_for_middle, maybe_for_end, maybe_for_body) => {
                if let Some(parent) = parent_ctx {
                    self.for_loop(
                        *loc,
                        parent.into().into(),
                        maybe_for_start,
                        maybe_for_middle,
                        maybe_for_end,
                        maybe_for_body,
                    );
                }
            }
            DoWhile(_loc, _while_stmt, _while_expr) => {
                todo!("do while not supported");
            }
            Continue(_loc) => {
                // TODO: We cheat in loops by just widening so continues dont matter yet
            }
            Break(_loc) => {
                // TODO: We cheat in loops by just widening so breaks dont matter yet
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
        };

        if let Some(parent) = parent_ctx {
            if let Node::Context(c) = self.node(parent.into()) {
                let adjusts = c.post_statement_range_adjs.clone();
                adjusts.into_iter().for_each(|(var, loc, increment)| {
                    let one_node = self.add_node(Node::Concrete(Concrete::from(U256::from(1))));
                    let one_node = self.add_node(Node::ContextVar(ContextVar::new_from_concrete(
                        Loc::Implicit,
                        one_node.into(),
                        self,
                    )));
                    let (_, _var) = self
                        .op(
                            loc,
                            var.latest_version(self),
                            one_node.into(),
                            parent.into().into(),
                            if increment {
                                RangeOp::Add
                            } else {
                                RangeOp::Sub
                            },
                            true,
                        )
                        .expect_single();
                });
                ContextNode::from(parent.into())
                    .underlying_mut(self)
                    .post_statement_range_adjs = vec![];
            }
        }
    }

    fn return_match(&mut self, loc: &Loc, paths: &ExprRet) {
        match paths {
            ExprRet::CtxKilled => {}
            ExprRet::Single((ctx, expr)) | ExprRet::SingleLiteral((ctx, expr)) => {
                self.add_edge(
                    ContextVarNode::from(*expr).latest_version(self),
                    *ctx,
                    Edge::Context(ContextEdge::Return),
                );
                ctx.add_return_node(*loc, ContextVarNode::from(*expr).latest_version(self), self);
            }
            ExprRet::Multi(rets) => {
                rets.iter().for_each(|expr_ret| {
                    let (ctx, expr) = expr_ret.expect_single();
                    self.add_edge(
                        ContextVarNode::from(expr).latest_version(self),
                        ctx,
                        Edge::Context(ContextEdge::Return),
                    );
                    ctx.add_return_node(
                        *loc,
                        ContextVarNode::from(expr).latest_version(self),
                        self,
                    );
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
            (ExprRet::CtxKilled, _) => {}
            (_, Some(ExprRet::CtxKilled)) => {}
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
                    MemberAccess(loc, _member_expr, _ident) => {
                        let (_func_ctx, func_idx) = match self.parse_ctx_expr(func_expr, ctx) {
                            ExprRet::Single((ctx, idx)) => (ctx, idx),
                            m @ ExprRet::Multi(_) => m.expect_single(),
                            ExprRet::CtxKilled => return ExprRet::CtxKilled,
                            e => todo!("got fork in func call: {:?}", e),
                        };

                        let inputs = ExprRet::Multi(
                            input_exprs
                                .iter()
                                .map(|expr| self.parse_ctx_expr(expr, ctx))
                                .collect(),
                        );

                        self.func_call(
                            ctx,
                            *loc,
                            &inputs,
                            ContextVarNode::from(func_idx)
                                .ty(self)
                                .func_node(self)
                                .expect(""),
                        )
                    }
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
            PreIncrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx);
                self.match_in_de_crement(true, true, *loc, &resp)
            }
            PostIncrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx);
                self.match_in_de_crement(false, true, *loc, &resp)
            }
            PreDecrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx);
                self.match_in_de_crement(true, false, *loc, &resp)
            }
            PostDecrement(loc, expr) => {
                let resp = self.parse_ctx_expr(expr, ctx);
                self.match_in_de_crement(false, false, *loc, &resp)
            }

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

    fn match_in_de_crement(
        &mut self,
        pre: bool,
        increment: bool,
        loc: Loc,
        rhs: &ExprRet,
    ) -> ExprRet {
        match rhs {
            ExprRet::CtxKilled => ExprRet::CtxKilled,
            ExprRet::SingleLiteral((ctx, var)) => {
                ContextVarNode::from(*var).try_increase_size(self);
                self.match_in_de_crement(pre, increment, loc, &ExprRet::Single((*ctx, *var)))
            }
            ExprRet::Single((ctx, var)) => {
                let cvar = ContextVarNode::from(*var);
                let elem = Elem::Dynamic(Dynamic::new(cvar.into(), loc));
                let one = Elem::from(Concrete::from(U256::from(1))).cast(elem);
                if let Some(r) = cvar.range(self) {
                    if increment {
                        if pre {
                            let new_cvar = self.advance_var_in_ctx(cvar, loc, *ctx);
                            new_cvar.set_range_min(self, r.min + one.clone());
                            new_cvar.set_range_max(self, r.max + one);
                            ExprRet::Single((*ctx, new_cvar.into()))
                        } else {
                            ctx.underlying_mut(self)
                                .post_statement_range_adjs
                                .push((cvar, loc, increment));
                            ExprRet::Single((*ctx, cvar.into()))
                        }
                    } else if pre {
                        let new_cvar = self.advance_var_in_ctx(cvar, loc, *ctx);
                        new_cvar.set_range_min(self, r.min - one.clone());
                        new_cvar.set_range_max(self, r.max - one);
                        ExprRet::Single((*ctx, new_cvar.into()))
                    } else {
                        ctx.underlying_mut(self)
                            .post_statement_range_adjs
                            .push((cvar, loc, increment));
                        ExprRet::Single((*ctx, cvar.into()))
                    }
                } else {
                    panic!("No range in post-increment")
                }
            }
            ExprRet::Multi(inner) => ExprRet::Multi(
                inner
                    .iter()
                    .map(|expr| self.match_in_de_crement(pre, increment, loc, expr))
                    .collect(),
            ),
            ExprRet::Fork(w1, w2) => ExprRet::Fork(
                Box::new(self.match_in_de_crement(pre, increment, loc, w1)),
                Box::new(self.match_in_de_crement(pre, increment, loc, w2)),
            ),
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
            (ExprRet::CtxKilled, _) | (_, ExprRet::CtxKilled) => ExprRet::CtxKilled,
            (ExprRet::Single((_lhs_ctx, lhs)), ExprRet::SingleLiteral((rhs_ctx, rhs))) => {
                let lhs_cvar = ContextVarNode::from(*lhs).latest_version(self);
                let rhs_cvar = ContextVarNode::from(*rhs).latest_version(self);
                rhs_cvar.cast_from(&lhs_cvar, self);
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
