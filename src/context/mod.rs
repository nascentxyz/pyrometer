use crate::bin_op::BinOp;
use crate::require::Require;
use crate::{
    AnalyzerLike, BuiltInNode, Builtin, Concrete, ConcreteNode, DynBuiltin, DynamicRangeSide, Edge,
    FieldNode, FunctionNode, FunctionParamNode, FunctionReturnNode, Node, NodeIdx, Op, RangeElem,
    TypeNode, VarType,
};

use ethers_core::types::U256;
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{Expression, Loc, Statement};

pub mod var;
pub use var::*;
pub mod exprs;
pub use exprs::*;

pub mod analyzers;
pub use analyzers::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ContextEdge {
    // Control flow
    Context,
    Subcontext,
    Call,

    // Context Variables
    Variable,
    InheritedVariable,

    AttrAccess,
    Index,
    IndexAccess,

    // Variable incoming edges
    Assign,
    StorageAssign,
    MemoryAssign,
    Prev,

    // Control flow
    Return,

    // Range analysis
    Range,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContextNode(pub usize);
impl ContextNode {
    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl AnalyzerLike) -> &'a mut Context {
        match analyzer.node_mut(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Context {
        match analyzer.node(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    pub fn var_by_name(&self, analyzer: &impl AnalyzerLike, name: &str) -> Option<ContextVarNode> {
        analyzer
            .graph()
            .edges_directed((*self).into(), Direction::Incoming)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|edge| ContextVarNode::from(edge.source()))
            .filter_map(|cvar_node| {
                let cvar = cvar_node.underlying(analyzer);
                if cvar.name == name {
                    Some(cvar_node)
                } else {
                    None
                }
            })
            .take(1)
            .next()
    }

    pub fn vars(&self, analyzer: &impl AnalyzerLike) -> Vec<ContextVarNode> {
        analyzer
            .graph()
            .edges_directed((*self).into(), Direction::Incoming)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|edge| ContextVarNode::from(edge.source()))
            .collect()
    }

    pub fn latest_var_by_name(
        &self,
        analyzer: &impl AnalyzerLike,
        name: &str,
    ) -> Option<ContextVarNode> {
        if let Some(var) = self.var_by_name(analyzer, name) {
            Some(var.latest_version(analyzer))
        } else {
            None
        }
    }

    pub fn new_tmp(&self, analyzer: &mut impl AnalyzerLike) -> usize {
        let context = self.underlying_mut(analyzer);
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        ret
    }
}
impl Into<NodeIdx> for ContextNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    pub tmp_var_ctr: usize,
    pub loc: Loc,
}

impl Context {
    pub fn new(loc: Loc) -> Self {
        Context {
            tmp_var_ctr: 0,
            loc,
        }
    }
}

impl<T> ContextBuilder for T where T: AnalyzerLike + Sized + BinOp + Require {}

pub trait ContextBuilder: AnalyzerLike + Sized + BinOp + Require {
    fn parse_ctx_statement(
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
                let ctx = Context::new(*loc);
                let ctx_node = self.add_node(Node::Context(ctx));

                if let Some(parent) = parent_ctx {
                    self.add_edge(ctx_node, parent, Edge::Context(ContextEdge::Context));
                }

                // optionally add named input and named outputs into context
                if let Some(parent) = parent_ctx.clone() {
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
                }

                statements
                    .iter()
                    .for_each(|stmt| self.parse_ctx_statement(stmt, *unchecked, Some(ctx_node)));
            }
            VariableDefinition(_loc, _var_decl, _maybe_expr) => {}
            Assembly {
                loc: _,
                dialect: _,
                flags: _,
                block: _yul_block,
            } => {}
            Args(_loc, _args) => {}
            If(_loc, _cond, _true_body, _maybe_false_body) => {}
            While(_loc, _cond, _body) => {}
            Expression(_loc, expr) => {
                if let Some(parent) = parent_ctx {
                    let expr_nodes = self.parse_ctx_expr(expr, ContextNode::from(parent.into()));
                    if expr_nodes.is_empty() {
                    } else {
                        self.add_edge(expr_nodes[0], parent, Edge::Context(ContextEdge::Call));
                    }
                }
            }
            For(_loc, _maybe_for_start, _maybe_for_middle, _maybe_for_end, _maybe_for_body) => {}
            DoWhile(_loc, _while_stmt, _while_expr) => {}
            Continue(_loc) => {}
            Break(_loc) => {}
            Return(_loc, maybe_ret_expr) => {
                if let Some(ret_expr) = maybe_ret_expr {
                    if let Some(parent) = parent_ctx {
                        let expr_node =
                            self.parse_ctx_expr(ret_expr, ContextNode::from(parent.into()))[0];
                        self.add_edge(expr_node, parent, Edge::Context(ContextEdge::Return));
                    }
                }
            }
            Revert(_loc, _maybe_err_path, _exprs) => {}
            RevertNamedArgs(_loc, _maybe_err_path, _named_args) => {}
            Emit(_loc, _emit_expr) => {}
            Try(_loc, _try_expr, _maybe_returns, _clauses) => {}
            Error(_loc) => {}
        }
    }

    fn parse_ctx_expr(&mut self, expr: &Expression, ctx: ContextNode) -> Vec<NodeIdx> {
        use Expression::*;
        println!("ctx_expr: {:?}", expr);
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone()) {
                    if let Some(idx) = self.builtins().get(&builtin) {
                        vec![*idx]
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins_mut().insert(builtin, idx);
                        vec![idx]
                    }
                } else {
                    todo!("??")
                }
            }
            Variable(ident) => {
                if let Some(cvar) = ctx.latest_var_by_name(self, &ident.name) {
                    vec![self.advance_var(cvar, ident.loc).0.into()]
                } else {
                    if let Some(idx) = self.user_types().get(&ident.name) {
                        vec![*idx]
                    } else {
                        if let Some(func) = self.builtin_fns().get(&ident.name) {
                            let (inputs, outputs) = self
                                .builtin_fn_inputs()
                                .get(&ident.name)
                                .expect("builtin func but no inputs")
                                .clone();
                            let func_node = self.add_node(Node::Function(func.clone()));
                            inputs.into_iter().for_each(|input| {
                                let input_node = self.add_node(input);
                                self.add_edge(input_node, func_node, Edge::FunctionParam);
                            });
                            outputs.into_iter().for_each(|output| {
                                let output_node = self.add_node(output);
                                self.add_edge(output_node, func_node, Edge::FunctionReturn);
                            });
                            vec![func_node]
                        } else {
                            let node = self.add_node(Node::Unresolved(ident.clone()));
                            self.user_types_mut().insert(ident.name.clone(), node);
                            vec![node]
                        }
                    }
                }
            }
            ArraySubscript(_loc, ty_expr, None) => {
                let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = DynBuiltin::Array(var_type);
                    if let Some(idx) = self.dyn_builtins().get(&dyn_b) {
                        vec![*idx]
                    } else {
                        let idx = self.add_node(Node::DynBuiltin(dyn_b.clone()));
                        self.dyn_builtins_mut().insert(dyn_b, idx);
                        vec![idx]
                    }
                } else {
                    todo!("???")
                }
            }
            ArraySubscript(loc, ty_expr, Some(index_expr)) => {
                println!("index: {:#?}", index_expr);
                let inner_ty = self.parse_ctx_expr(&ty_expr, ctx)[0];
                let index_ty = self.parse_ctx_expr(&index_expr, ctx)[0];

                let index_var = ContextVar {
                    loc: Some(*loc),
                    name: ContextVarNode::from(index_ty).name(self),
                    display_name: ContextVarNode::from(index_ty).display_name(self),
                    storage: ContextVarNode::from(inner_ty).storage(self).clone(),
                    tmp_of: None,
                    ty: ContextVarNode::from(inner_ty)
                        .ty(self)
                        .array_underlying_ty(self),
                };

                let cvar_idx = self.add_node(Node::ContextVar(index_var));
                self.add_edge(cvar_idx, inner_ty, Edge::Context(ContextEdge::IndexAccess));

                self.add_edge(index_ty, cvar_idx, Edge::Context(ContextEdge::Index));

                vec![cvar_idx]
            }
            NumberLiteral(loc, int, exp) => {
                // TODO: improve this to actually work

                let int = U256::from_dec_str(&int).unwrap();
                let val = if !exp.is_empty() {
                    let exp = U256::from_dec_str(&exp).unwrap();
                    int.pow(exp)
                } else {
                    int
                };
                let concrete_node =
                    ConcreteNode::from(self.add_node(Node::Concrete(Concrete::Uint(256, val))));
                let ccvar =
                    Node::ContextVar(ContextVar::new_from_concrete(*loc, concrete_node, self));
                vec![self.add_node(ccvar)]
            }
            MemberAccess(loc, member_expr, ident) => {
                let member_idx = self.parse_ctx_expr(member_expr, ctx)[0];
                match self.node(member_idx) {
                    Node::ContextVar(cvar) => match &cvar.ty {
                        VarType::User(TypeNode::Struct(struct_node)) => {
                            let field = self
                                .graph()
                                .edges_directed(struct_node.0.into(), Direction::Incoming)
                                .filter(|edge| *edge.weight() == Edge::Field)
                                .map(|edge| FieldNode::from(edge.source()))
                                .collect::<Vec<FieldNode>>()
                                .iter()
                                .filter_map(|field_node| {
                                    let field = field_node.underlying(self);
                                    if field.name.as_ref().expect("field wasnt named").name
                                        == ident.name
                                    {
                                        Some(field)
                                    } else {
                                        None
                                    }
                                })
                                .take(1)
                                .next()
                                .expect(&format!(
                                    "No field with name {:?} in struct: {:?}",
                                    ident.name,
                                    struct_node.name(self)
                                ));
                            if let Some(field_cvar) =
                                ContextVar::maybe_new_from_field(self, *loc, cvar, field.clone())
                            {
                                let fc_node = self.add_node(Node::ContextVar(field_cvar));
                                self.add_edge(
                                    fc_node,
                                    member_idx,
                                    Edge::Context(ContextEdge::AttrAccess),
                                );
                                return vec![fc_node];
                            }
                        }
                        e => todo!("member access: {:?}", e),
                    },
                    _ => todo!(),
                }
                vec![member_idx]
            }
            Less(loc, lhs, rhs) => {
                let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(lhs, ctx)[0]);
                let rhs_cvar = ContextVarNode::from(self.parse_ctx_expr(rhs, ctx)[0]);

                let out_var = ContextVar {
                    loc: Some(*loc),
                    name: format!(
                        "{} < {}__{}",
                        lhs_cvar.name(self),
                        rhs_cvar.name(self),
                        ctx.new_tmp(self)
                    ),
                    display_name: format!(
                        "{} < {}__{}",
                        lhs_cvar.display_name(self),
                        rhs_cvar.display_name(self),
                        ctx.new_tmp(self)
                    ),
                    storage: None,
                    tmp_of: None,
                    ty: VarType::BuiltIn(
                        BuiltInNode::from(self.builtin_or_add(Builtin::Bool)),
                        None,
                    ),
                };

                vec![self.add_node(Node::ContextVar(out_var))]
            }
            FunctionCall(_loc, func_expr, input_exprs) => {
                let func_idx = self.parse_ctx_expr(func_expr, ctx)[0];

                if let Some(func_name) = &FunctionNode::from(func_idx).underlying(self).name {
                    if func_name.name == "require" {
                        self.handle_require(input_exprs, ctx);
                        return vec![];
                    }
                }

                let _inputs: Vec<_> = input_exprs
                    .into_iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                // todo!("func call")
                vec![func_idx]
            }
            Add(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Add, false)
            }
            AssignAdd(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Add, true)
            }
            Subtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Sub, false)
            }
            AssignSubtract(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Sub, true)
            }
            Multiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mul, false)
            }
            AssignMultiply(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mul, true)
            }
            Divide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Div, false)
            }
            AssignDivide(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Div, true)
            }
            Modulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mod, false)
            }
            AssignModulo(loc, lhs_expr, rhs_expr) => {
                self.op_expr(*loc, lhs_expr, rhs_expr, ctx, Op::Mod, true)
            }
            Assign(loc, lhs_expr, rhs_expr) => self.assign(*loc, lhs_expr, rhs_expr, ctx),
            e => todo!("{:?}", e),
        }
    }

    fn assign(
        &mut self,
        loc: Loc,
        lhs_expr: &Expression,
        rhs_expr: &Expression,
        ctx: ContextNode,
    ) -> Vec<NodeIdx> {
        let lhs_cvar = ContextVarNode::from(self.parse_ctx_expr(&lhs_expr, ctx)[0]);
        let rhs_cvar = ContextVarNode::from(self.parse_ctx_expr(rhs_expr, ctx)[0]);

        let (new_lower_bound, new_upper_bound) = if let Some(range) = rhs_cvar.range(self) {
            (range.min, range.max)
        } else {
            (
                RangeElem::Dynamic(rhs_cvar.into(), DynamicRangeSide::Min, loc),
                RangeElem::Dynamic(rhs_cvar.into(), DynamicRangeSide::Max, loc),
            )
        };

        let new_lhs = self.advance_var(lhs_cvar, loc);
        new_lhs.set_range_min(self, new_lower_bound);
        new_lhs.set_range_max(self, new_upper_bound);
        vec![new_lhs.into()]
    }

    fn advance_var(&mut self, cvar_node: ContextVarNode, loc: Loc) -> ContextVarNode {
        let mut new_cvar = cvar_node.underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode)
    }

    fn advance_var_underlying(&mut self, cvar_node: ContextVarNode, loc: Loc) -> &mut ContextVar {
        let mut new_cvar = cvar_node.underlying(self).clone();
        new_cvar.loc = Some(loc);
        let new_cvarnode = self.add_node(Node::ContextVar(new_cvar));
        self.add_edge(new_cvarnode, cvar_node.0, Edge::Context(ContextEdge::Prev));
        ContextVarNode::from(new_cvarnode).underlying_mut(self)
    }
}
