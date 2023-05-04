use crate::analyzer::GraphError;
use crate::analyzer::{AnalyzerLike, GraphLike, Search};
use crate::as_dot_str;
use crate::nodes::FunctionNode;
use crate::AsDotStr;
use crate::ContractNode;
use crate::StructNode;
use petgraph::dot::Dot;
use std::collections::BTreeSet;

use crate::{Edge, Node, NodeIdx};

use solang_parser::pt::Loc;
use std::collections::BTreeMap;

mod var;
pub use var::*;
mod expr_ret;
pub use expr_ret::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum CallFork {
    Call(ContextNode),
    Fork(ContextNode, ContextNode),
}

impl CallFork {
    pub fn maybe_call(&self) -> Option<ContextNode> {
        match self {
            CallFork::Call(c) => Some(*c),
            _ => None,
        }
    }

    pub fn maybe_fork(&self) -> Option<(ContextNode, ContextNode)> {
        match self {
            CallFork::Fork(w1, w2) => Some((*w1, *w2)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ContextEdge {
    // Control flow
    Context,
    Subcontext,
    ContextFork,
    ContextMerge,
    Call,

    // Context Variables
    Variable,
    InheritedVariable,

    AttrAccess,
    Index,
    IndexAccess,
    FuncAccess,

    // Variable incoming edges
    Assign,
    StorageAssign,
    MemoryAssign,
    Prev,

    // Control flow
    Return,
    Continue,
    InputVariable,
    ReturnAssign(bool),

    // Range analysis
    Range,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ModifierState {
    pub num: usize,
    pub loc: Loc,
    pub parent_fn: FunctionNode,
    pub parent_caller_ctx: ContextNode,
    pub parent_ctx: ContextNode,
    pub renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
}

impl ModifierState {
    pub fn new(
        num: usize,
        loc: Loc,
        parent_fn: FunctionNode,
        parent_ctx: ContextNode,
        parent_caller_ctx: ContextNode,
        renamed_inputs: BTreeMap<ContextVarNode, ContextVarNode>,
    ) -> Self {
        Self {
            num,
            loc,
            parent_fn,
            parent_ctx,
            parent_caller_ctx,
            renamed_inputs,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    /// The function associated with this context
    pub parent_fn: FunctionNode,
    /// Whether this function call is actually a modifier call
    pub modifier_state: Option<ModifierState>,
    /// An optional parent context (i.e. this context is a fork or subcontext of another previous context)
    pub parent_ctx: Option<ContextNode>,
    /// Variables whose bounds are required to be met for this context fork to exist. i.e. a conditional operator
    /// like an if statement
    pub ctx_deps: BTreeMap<String, ContextVarNode>,
    /// A string that represents the path taken from the root context (i.e. `fn_entry.fork.1`)
    pub path: String,
    /// Denotes whether this context was killed by an unsatisfiable require, assert, etc. statement
    pub killed: Option<Loc>,
    /// Denotes whether this context is a fork of another context
    pub is_fork: bool,
    /// Denotes whether this context is the result of a internal function call, and points to the FunctionNode
    pub fn_call: Option<FunctionNode>,
    /// Denotes whether this context is the result of a internal function call, and points to the FunctionNode
    pub ext_fn_call: Option<FunctionNode>,
    /// The child context. This is either of the form `Call(child_context)` or `Fork(world1, world2)`. Once
    /// a child is defined we should *never* evaluate an expression in this context.
    pub child: Option<CallFork>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Vec<(Loc, ContextVarNode)>,
    /// Range adjustments to occur after the statement finishes. Useful for post in/decrement
    pub post_statement_range_adjs: Vec<(ContextVarNode, Loc, bool)>,
    /// Depth tracker
    pub depth: usize,
    pub lhs_expr: Option<ExprRet>,
    pub rhs_expr: Option<ExprRet>,
    pub expr_ret_stack: Option<ExprRet>,
}

impl Context {
    /// Creates a new context from a function
    pub fn new(parent_fn: FunctionNode, fn_name: String, loc: Loc) -> Self {
        Context {
            parent_fn,
            parent_ctx: None,
            path: fn_name,
            tmp_var_ctr: 0,
            killed: None,
            ctx_deps: Default::default(),
            is_fork: false,
            fn_call: None,
            ext_fn_call: None,
            child: None,
            ret: vec![],
            loc,
            modifier_state: None,
            post_statement_range_adjs: vec![],
            depth: 0,
            expr_ret_stack: None,
            lhs_expr: None,
            rhs_expr: None,
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        parent_ctx: ContextNode,
        returning_ctx: Option<ContextNode>,
        loc: Loc,
        fork_expr: Option<&str>,
        fn_call: Option<FunctionNode>,
        fn_ext: bool,
        analyzer: &impl AnalyzerLike,
        modifier_state: Option<ModifierState>,
    ) -> Result<Self, GraphError> {
        let mut depth = parent_ctx.underlying(analyzer)?.depth + 1;

        if analyzer.max_depth() < depth {
            return Err(GraphError::MaxStackDepthReached(format!(
                "Stack depth limit reached: {}",
                depth - 1
            )));
        }
        let (fn_name, ext_fn_call, fn_call) = if let Some(fn_call) = fn_call {
            if fn_ext {
                (fn_call.name(analyzer)?, Some(fn_call), None)
            } else {
                (fn_call.name(analyzer)?, None, Some(fn_call))
            }
        } else {
            ("anonymous_fn_call".to_string(), None, None)
        };

        let path = format!(
            "{}.{}",
            parent_ctx.underlying(analyzer)?.path,
            if let Some(ref fork_expr) = fork_expr {
                format!("fork{{ {} }}", fork_expr)
            } else if let Some(returning_ctx) = returning_ctx {
                depth = depth.saturating_sub(2);
                format!(
                    "resume{{ {} }}",
                    returning_ctx.associated_fn_name(analyzer)?
                )
            } else {
                fn_name
            }
        );

        tracing::trace!("new subcontext path: {path}, depth: {depth}");
        Ok(Context {
            parent_fn: parent_ctx.underlying(analyzer)?.parent_fn,
            parent_ctx: Some(parent_ctx),
            path,
            is_fork: fork_expr.is_some(),
            fn_call,
            ext_fn_call,
            ctx_deps: parent_ctx.underlying(analyzer)?.ctx_deps.clone(),
            killed: None,
            child: None,
            tmp_var_ctr: parent_ctx.underlying(analyzer)?.tmp_var_ctr,
            ret: vec![],
            loc,
            modifier_state,
            post_statement_range_adjs: vec![],
            depth,
            expr_ret_stack: if fork_expr.is_some() {
                parent_ctx.underlying(analyzer)?.expr_ret_stack.clone()
            } else {
                None
            },
            lhs_expr: None,
            rhs_expr: None,
        })
    }

    /// Set the child context to a fork
    pub fn set_child_fork(&mut self, world1: ContextNode, world2: ContextNode) -> bool {
        if self.child.is_some() {
            false
        } else {
            self.child = Some(CallFork::Fork(world1, world2));
            true
        }
    }

    /// Set the child context to a call
    pub fn set_child_call(&mut self, call_ctx: ContextNode) -> bool {
        if self.child.is_some() {
            false
        } else {
            self.child = Some(CallFork::Call(call_ctx));
            true
        }
    }

    pub fn delete_child(&mut self) {
        self.child = None;
    }

    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }
}

#[derive(Debug, Clone)]
pub struct CtxTree {
    pub node: ContextNode,
    pub lhs: Option<Box<CtxTree>>,
    pub rhs: Option<Box<CtxTree>>,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    // pub fn called_functions(&self, analyzer: &impl GraphLike) -> Result<Vec<FunctionNode>, GraphError> {
    //     self.underlying(analyzer)?.children.iter().filter_map(|child| {
    //         match child.maybe_call()?.underlying(analyzer) {
    //             Ok(underlying) => {
    //                 match (underlying.fn_call, underlying.ext_fn_call) {
    //                     (Some(fn_call), _) => Some(Ok(fn_call)),
    //                     (_, Some(ext_fn_call)) => Some(Ok(ext_fn_call)),
    //                     (None, None) => None
    //                 }
    //             }
    //             Err(_) => None
    //         }
    //     }).collect()
    // }

    pub fn push_rhs_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        match &mut underlying_mut.rhs_expr {
            Some(s @ ExprRet::Single(_)) => {
                underlying_mut.rhs_expr = Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(s @ ExprRet::SingleLiteral(_)) => {
                underlying_mut.rhs_expr = Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(ExprRet::Multi(ref mut inner)) => {
                inner.push(expr_ret);
            }
            Some(ExprRet::CtxKilled) => {
                underlying_mut.lhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.rhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.expr_ret_stack = Some(ExprRet::CtxKilled);
            }
            None => {
                underlying_mut.rhs_expr = Some(expr_ret);
            }
        }
        Ok(())
    }

    pub fn pop_rhs_expr(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        Ok(underlying_mut.rhs_expr.take())
    }

    pub fn push_lhs_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        match &mut underlying_mut.lhs_expr {
            Some(s @ ExprRet::Single(_)) => {
                underlying_mut.lhs_expr = Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(s @ ExprRet::SingleLiteral(_)) => {
                underlying_mut.lhs_expr = Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(ExprRet::Multi(ref mut inner)) => {
                inner.push(expr_ret);
            }
            Some(ExprRet::CtxKilled) => {
                underlying_mut.lhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.rhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.expr_ret_stack = Some(ExprRet::CtxKilled);
            }
            None => {
                underlying_mut.lhs_expr = Some(expr_ret);
            }
        }
        Ok(())
    }

    pub fn pop_lhs_expr(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        Ok(underlying_mut.lhs_expr.take())
    }

    pub fn push_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        match &mut underlying_mut.expr_ret_stack {
            Some(s @ ExprRet::Single(_)) => {
                underlying_mut.expr_ret_stack =
                    Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(s @ ExprRet::SingleLiteral(_)) => {
                underlying_mut.expr_ret_stack =
                    Some(ExprRet::Multi(vec![s.clone(), expr_ret]).flatten());
            }
            Some(ExprRet::Multi(ref mut inner)) => {
                inner.push(expr_ret);
            }
            Some(ExprRet::CtxKilled) => {
                underlying_mut.lhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.rhs_expr = Some(ExprRet::CtxKilled);
                underlying_mut.expr_ret_stack = Some(ExprRet::CtxKilled);
            }
            None => {
                underlying_mut.expr_ret_stack = Some(expr_ret);
            }
        }
        Ok(())
    }

    pub fn maybe_move_expr(
        &self,
        expr: ExprRet,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ExprRet, GraphError> {
        match expr {
            ExprRet::SingleLiteral(var) => Ok(ExprRet::SingleLiteral(
                self.maybe_move_var(var.into(), loc, analyzer)?.into(),
            )),
            ExprRet::Single(var) => Ok(ExprRet::Single(
                self.maybe_move_var(var.into(), loc, analyzer)?.into(),
            )),
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .iter()
                    .map(|i| self.maybe_move_expr(i.clone(), loc, analyzer))
                    .collect::<Result<_, _>>()?,
            )),
            e => Ok(e),
        }
    }

    pub fn maybe_move_var(
        &self,
        var: ContextVarNode,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ContextVarNode, GraphError> {
        if let Some(ctx) = var.maybe_ctx(analyzer) {
            if ctx != *self {
                let mut new_cvar = var.latest_version(analyzer).underlying(analyzer)?.clone();
                new_cvar.loc = Some(loc);

                let new_cvarnode = analyzer.add_node(Node::ContextVar(new_cvar));
                analyzer.add_edge(new_cvarnode, *self, Edge::Context(ContextEdge::Variable));
                analyzer.add_edge(
                    new_cvarnode,
                    var.0,
                    Edge::Context(ContextEdge::InheritedVariable),
                );
                Ok(new_cvarnode.into())
            } else {
                Ok(var)
            }
        } else {
            Ok(var)
        }
    }

    pub fn pop_expr(
        &self,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        if let Some(expr) = underlying_mut.expr_ret_stack.take() {
            Ok(Some(self.maybe_move_expr(expr, loc, analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn vars_assigned_from_fn_ret(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        self.local_vars(analyzer)
            .iter()
            .flat_map(|var| var.return_assignments(analyzer))
            .collect()
    }

    pub fn vars_assigned_from_ext_fn_ret(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        // println!("vars_assigned_from_ext_fn_ret: {}", self.path(analyzer));
        self.local_vars(analyzer)
            .iter()
            .flat_map(|var| var.ext_return_assignments(analyzer))
            .collect()
    }

    pub fn depth(&self, analyzer: &impl GraphLike) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    // pub fn into_ctx_tree(&self, analyzer: &impl GraphLike) -> CtxTree {
    //     let forks = self.forks(analyzer).unwrap();
    //     CtxTree {
    //         node: *self,
    //         lhs: if !forks.is_empty() {
    //             Some(Box::new(forks[0].into_ctx_tree(analyzer)))
    //         } else {
    //             None
    //         },
    //         rhs: if !forks.is_empty() {
    //             Some(Box::new(forks[1].into_ctx_tree(analyzer)))
    //         } else {
    //             None
    //         },
    //     }
    // }

    /// *All* subcontexts (including subcontexts of subcontexts, recursively)
    pub fn subcontexts(&self, analyzer: &impl GraphLike) -> Vec<ContextNode> {
        let underlying = self.underlying(analyzer).unwrap();
        match underlying.child {
            Some(CallFork::Call(c)) => vec![c],
            Some(CallFork::Fork(w1, w2)) => vec![w1, w2],
            None => vec![],
        }
    }

    /// Gets the associated contract for the function for the context
    pub fn associated_contract(
        &self,
        analyzer: &(impl GraphLike + AnalyzerLike),
    ) -> Result<ContractNode, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer)
            .expect("No associated contract for context"))
    }

    /// Tries to get the associated function for the context
    pub fn maybe_associated_contract(
        &self,
        analyzer: &(impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ContractNode>, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer))
    }

    pub fn associated_source(&self, analyzer: &impl GraphLike) -> NodeIdx {
        analyzer
            .search_for_ancestor(self.0.into(), &Edge::Part)
            .expect("No associated source?")
    }

    pub fn associated_source_unit_part(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<NodeIdx, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .associated_source_unit_part(analyzer))
    }

    /// Gets visible functions
    pub fn visible_modifiers(
        &self,
        analyzer: &(impl GraphLike + AnalyzerLike),
    ) -> Result<Vec<FunctionNode>, GraphError> {
        // TODO: filter privates
        let source = self.associated_source(analyzer);
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            let mut modifiers = contract.modifiers(analyzer);
            // extend with free floating functions
            modifiers.extend(
                analyzer
                    .search_children_depth(source, &Edge::Modifier, 1, 0)
                    .into_iter()
                    .map(FunctionNode::from)
                    .collect::<Vec<_>>(),
            );

            // extend with inherited functions
            let inherited_contracts =
                analyzer.search_children(contract.0.into(), &Edge::InheritedContract);
            // println!("inherited: [{:#?}]", inherited_contracts.iter().map(|i| ContractNode::from(*i).name(analyzer)).collect::<Vec<_>>());
            modifiers.extend(
                inherited_contracts
                    .into_iter()
                    .flat_map(|inherited_contract| {
                        ContractNode::from(inherited_contract).modifiers(analyzer)
                    })
                    .collect::<Vec<_>>(),
            );

            let mut mapping: BTreeMap<String, BTreeSet<FunctionNode>> = BTreeMap::new();
            for modifier in modifiers.iter() {
                let entry = mapping.entry(modifier.name(analyzer)?).or_default();
                entry.insert(*modifier);
            }
            mapping
                .into_values()
                .map(|modifier_set| {
                    let as_vec = modifier_set.iter().collect::<Vec<_>>();

                    if as_vec.len() > 2 {
                        println!("{}", as_vec.iter().map(|i| i.name(analyzer).unwrap()).collect::<Vec<_>>().join(", "));
                        panic!("3+ visible functions with the same name. This is invalid solidity, {as_vec:#?}")
                    } else if as_vec.len() == 2 {
                        as_vec[0].get_overriding(as_vec[1], analyzer)
                    } else {
                        Ok(*as_vec[0])
                    }
                })
                .collect()
        } else {
            // we are in a free floating function, only look at free floating functions
            let source = self.associated_source(analyzer);
            Ok(analyzer
                .search_children_depth(source, &Edge::Modifier, 1, 0)
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>())
        }
    }

    /// Gets visible functions
    pub fn visible_funcs(
        &self,
        analyzer: &(impl GraphLike + AnalyzerLike),
    ) -> Result<Vec<FunctionNode>, GraphError> {
        // TODO: filter privates
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            let mut funcs = contract.funcs(analyzer);
            // extend with free floating functions
            funcs.extend(
                analyzer
                    .search_children_depth(analyzer.entry(), &Edge::Func, 2, 0)
                    .into_iter()
                    .map(FunctionNode::from)
                    .collect::<Vec<_>>(),
            );

            // extend with inherited functions
            let inherited_contracts = analyzer.search_children_exclude_via(
                contract.0.into(),
                &Edge::InheritedContract,
                &[Edge::Func],
            );
            funcs.extend(
                inherited_contracts
                    .into_iter()
                    .flat_map(|inherited_contract| {
                        ContractNode::from(inherited_contract).funcs(analyzer)
                    })
                    .collect::<Vec<_>>(),
            );

            let mut mapping: BTreeMap<String, BTreeSet<FunctionNode>> = BTreeMap::new();
            for func in funcs.iter() {
                let entry = mapping.entry(func.name(analyzer)?).or_default();
                entry.insert(*func);
            }
            mapping
                .into_values()
                .map(|funcs_set| {
                    let as_vec = funcs_set.iter().collect::<Vec<_>>();

                    if as_vec.len() > 2 {
                        println!("{}", as_vec.iter().map(|i| i.name(analyzer).unwrap()).collect::<Vec<_>>().join(", "));
                        panic!("3+ visible functions with the same name. This is invalid solidity, {as_vec:#?}")
                    } else if as_vec.len() == 2 {
                        as_vec[0].get_overriding(as_vec[1], analyzer)
                    } else {
                        Ok(*as_vec[0])
                    }
                })
                .collect()
        } else {
            // we are in a free floating function, only look at free floating functions
            Ok(analyzer
                .search_children_depth(analyzer.entry(), &Edge::Func, 2, 0)
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>())
        }
    }

    /// Gets all visible functions
    pub fn source_funcs(&self, analyzer: &impl GraphLike) -> Vec<FunctionNode> {
        // TODO: filter privates
        let source = self.associated_source(analyzer);
        analyzer
            .search_children(source, &Edge::Func)
            .into_iter()
            .map(FunctionNode::from)
            .collect::<Vec<_>>()
    }

    /// Gets all visible structs
    pub fn visible_structs(&self, analyzer: &impl GraphLike) -> Vec<StructNode> {
        // TODO: filter privates
        let source = self.associated_source(analyzer);
        analyzer
            .search_children_exclude_via(source, &Edge::Struct, &[Edge::Func])
            .into_iter()
            .map(StructNode::from)
            .collect::<Vec<_>>()
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &impl GraphLike) -> Result<FunctionNode, GraphError> {
        let underlying = self.underlying(analyzer)?;
        if let Some(fn_call) = underlying.fn_call {
            Ok(fn_call)
        } else if let Some(ext_fn_call) = underlying.ext_fn_call {
            Ok(ext_fn_call)
        } else {
            Ok(underlying.parent_fn)
        }
    }

    /// Checks whether a function is external to the current context
    pub fn is_fn_ext(
        &self,
        fn_node: FunctionNode,
        analyzer: &(impl GraphLike + AnalyzerLike),
    ) -> Result<bool, GraphError> {
        match fn_node.maybe_associated_contract(analyzer) {
            None => Ok(false),
            Some(fn_ctrt) => {
                if let Some(self_ctrt) = self
                    .associated_fn(analyzer)?
                    .maybe_associated_contract(analyzer)
                {
                    Ok(Some(self_ctrt) != Some(fn_ctrt)
                        && !self_ctrt
                            .underlying(analyzer)?
                            .inherits
                            .iter()
                            .any(|inherited| *inherited == fn_ctrt))
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        self.associated_fn(analyzer)?.name(analyzer)
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut (impl GraphLike + AnalyzerLike),
    ) -> Result<&'a mut Context, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Context, GraphError> {
        match analyzer.node(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets a variable by name in the context
    pub fn var_by_name(&self, analyzer: &impl GraphLike, name: &str) -> Option<ContextVarNode> {
        analyzer
            .find_child_exclude_via(
                self.0.into(),
                &Edge::Context(ContextEdge::Variable),
                &[
                    Edge::Context(ContextEdge::Prev),
                    Edge::Context(ContextEdge::Call),
                ],
                &|cvar_node, analyzer| {
                    if matches!(analyzer.node(cvar_node), Node::ContextVar(..)) {
                        let cvar_node = ContextVarNode::from(cvar_node);
                        let cvar = cvar_node.underlying(analyzer).unwrap();
                        if cvar.name == name {
                            Some(cvar_node.into())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                },
            )
            .map(|idx| idx.into())
    }

    pub fn var_by_name_or_recurse(
        &self,
        analyzer: &impl GraphLike,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = analyzer
            .search_children_depth(self.0.into(), &Edge::Context(ContextEdge::Variable), 1, 0)
            .into_iter()
            .filter_map(|cvar_node| {
                let cvar_node = ContextVarNode::from(cvar_node);
                let cvar = cvar_node.underlying(analyzer).unwrap();
                if cvar.name == name {
                    Some(cvar_node)
                } else {
                    None
                }
            })
            .take(1)
            .next()
        {
            Ok(Some(var))
        } else if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            parent.var_by_name_or_recurse(analyzer, name)
        } else {
            Ok(None)
        }
    }

    /// Gets all variables associated with a context
    pub fn vars(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        analyzer
            .search_children_depth(self.0.into(), &Edge::Context(ContextEdge::Variable), 1, 0)
            .into_iter()
            .map(ContextVarNode::from)
            .collect()
    }

    /// Gets all variables associated with a context
    pub fn local_vars(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        // analyzer
        //     .graph()
        //     .edges_directed(self.0.into(), Direction::Incoming)
        //     .filter_map(|edge| {
        //         if edge.weight() == &Edge::Context(ContextEdge::Variable) {
        //             Some(edge.source())
        //         } else {
        //             None
        //         }
        //     })
        //     .map(ContextVarNode::from)
        //     .collect()
        self.vars(analyzer)
    }

    /// Gets the latest version of a variable associated with a context
    pub fn latest_var_by_name(
        &self,
        analyzer: &impl GraphLike,
        name: &str,
    ) -> Option<ContextVarNode> {
        self.var_by_name(analyzer, name)
            .map(|var| var.latest_version(analyzer))
    }

    /// Reads the current temporary counter and increments the counter
    pub fn new_tmp(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<usize, GraphError> {
        let context = self.underlying_mut(analyzer)?;
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        Ok(ret)
    }

    /// Returns all forks associated with the context
    pub fn calls(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        let descendents = self.descendents(analyzer)?;
        Ok(descendents
            .into_iter()
            .filter_map(|c| c.maybe_call())
            .collect())
    }

    /// Returns all forks associated with the context
    // pub fn forks(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
    // todo!()
    // let descendents = self.descendents(analyzer)?;
    // Ok(descendents.into_iter().filter_map(|c| c.maybe_fork()).collect())
    // }

    // /// Returns all *live* forks associated with the context
    // pub fn live_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
    //     let forks = self.forks(analyzer)?;
    //     let mut live = vec![];
    //     for fork in forks {
    //         if !fork.is_ended(analyzer)? {
    //             live.push(fork);
    //         }
    //     }
    //     Ok(live)
    // }

    /// Returns tail contexts associated with the context
    pub fn live_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        let edges = self.all_edges(analyzer)?;
        // println!("\nall edges: [\n{}]\n", edges.iter().map(|i| format!("   {},\n", i.path(analyzer))).collect::<Vec<_>>().join(""));
        Ok(edges
            .into_iter()
            .filter(|edge| !edge.killed_or_ret(analyzer).unwrap())
            .collect())
    }

    /// Returns tail contexts associated with the context
    pub fn all_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.all_edges(analyzer)?;
                    if call_edges.is_empty() {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.all_edges(analyzer)?;
                    if fork_edges.is_empty() {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.all_edges(analyzer)?;
                    if fork_edges.is_empty() {
                        lineage.push(w2)
                    } else {
                        lineage.extend(fork_edges);
                    }
                }
            }
            Ok(lineage)
        } else {
            Ok(vec![])
        }
    }

    pub fn descendents(&self, analyzer: &impl GraphLike) -> Result<Vec<CallFork>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut descendents = vec![child];
            match child {
                CallFork::Call(c) => descendents.extend(c.descendents(analyzer)?),
                CallFork::Fork(w1, w2) => {
                    descendents.extend(w1.descendents(analyzer)?);
                    descendents.extend(w2.descendents(analyzer)?);
                }
            }
            Ok(descendents)
        } else {
            Ok(vec![])
        }
    }

    /// Adds a fork to the context
    pub fn set_child_fork(
        &self,
        w1: ContextNode,
        w2: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        if !context.set_child_fork(w1, w2) {
            let child_str = match context.child {
                Some(CallFork::Fork(w1, w2)) => {
                    format!("fork {{ {}, {} }}", w1.path(analyzer), w2.path(analyzer))
                }
                Some(CallFork::Call(call)) => format!("call {{ {} }}", call.path(analyzer)),
                None => unreachable!(),
            };
            Err(GraphError::ChildRedefinition(format!(
            // panic!(
                "Tried to redefine a child context, parent: {}, current child: {}, new child: Fork({}, {})",
                self.path(analyzer),
                child_str,
                w1.path(analyzer),
                w2.path(analyzer),
            )
            ))
        } else {
            Ok(())
        }
    }

    /// Adds a child to the context
    pub fn set_child_call(
        &self,
        call: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        if !context.set_child_call(call) {
            let child_str = match context.child {
                Some(CallFork::Fork(w1, w2)) => {
                    format!("fork {{ {}, {} }}", w1.path(analyzer), w2.path(analyzer))
                }
                Some(CallFork::Call(call)) => format!("call {{ {} }}", call.path(analyzer)),
                None => unreachable!(),
            };
            Err(GraphError::ChildRedefinition(format!(
                // panic!(
                "Tried to redefine a child context, parent: {}, current child: {}, new child: {}",
                self.path(analyzer),
                child_str,
                call.path(analyzer)
            )))
        } else {
            Ok(())
        }
    }

    pub fn delete_child(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        context.delete_child();
        Ok(())
    }

    /// Kills the context by denoting it as killed. Recurses up the contexts and kills
    /// parent contexts if all subcontexts of that context are killed
    pub fn kill(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        kill_loc: Loc,
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        let child = context.child;
        let parent = context.parent_ctx;
        if context.killed.is_none() {
            context.killed = Some(kill_loc);
        }

        if let Some(child) = child {
            match child {
                CallFork::Call(call) => {
                    call.kill(analyzer, kill_loc)?;
                }
                CallFork::Fork(w1, w2) => {
                    w1.kill(analyzer, kill_loc)?;
                    w2.kill(analyzer, kill_loc)?;
                }
            }
        }

        if let Some(parent_ctx) = parent {
            parent_ctx.end_if_all_forks_ended(analyzer, kill_loc)?;
        }

        Ok(())
    }

    /// Kills if and only if all subcontexts are killed
    pub fn end_if_all_forks_ended(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        kill_loc: Loc,
    ) -> Result<(), GraphError> {
        if self.live_edges(analyzer)?.is_empty() {
            let context = self.underlying_mut(analyzer)?;
            if context.killed.is_none() {
                context.killed = Some(kill_loc);
            }
            if let Some(parent_ctx) = context.parent_ctx {
                parent_ctx.end_if_all_forks_ended(analyzer, kill_loc)?;
            }
        }
        Ok(())
    }

    /// Gets parent list
    pub fn parent_list(&self, analyzer: &impl GraphLike) -> Result<Vec<ContextNode>, GraphError> {
        let context = self.underlying(analyzer)?;
        let mut parents = vec![];
        if let Some(parent_ctx) = context.parent_ctx {
            parents.push(parent_ctx);
            parents.extend(parent_ctx.parent_list(analyzer)?);
        }
        Ok(parents)
    }

    pub fn recursive_calls(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        // Ok(
        let calls = self.calls(analyzer)?;
        Ok(calls
            .iter()
            .flat_map(|call| {
                let mut inner_calls = call.recursive_calls(analyzer).unwrap();
                inner_calls.insert(0, *call);
                inner_calls
            })
            .collect::<Vec<ContextNode>>())
    }

    /// Gets the lineage for a context
    /// A lineage is of the form `[ancestor N, .. , ancestor0, SELF, call0, .., call N]`. It
    /// gives the user a full picture of control flow
    pub fn lineage(
        &self,
        _analyzer: &impl GraphLike,
        _entry: bool,
    ) -> Result<Vec<ContextNode>, GraphError> {
        todo!()
    }

    pub fn terminal_child_list(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        let calls = self.calls(analyzer)?;
        if calls.is_empty() {
            Ok(vec![*self])
        } else {
            let mut children = vec![];

            for child in calls.into_iter() {
                children.extend(child.terminal_child_list(analyzer)?)
            }
            Ok(children)
        }
    }

    /// Returns whether the context is killed
    pub fn is_killed(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.killed.is_some())
    }

    /// Returns whether the context is killed
    pub fn is_ended(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.child.is_some() || underlying.killed.is_some() || !underlying.ret.is_empty())
    }

    pub fn killed_or_ret(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.killed.is_some()
            || (!underlying.ret.is_empty() && underlying.modifier_state.is_none()))
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(&self, analyzer: &impl GraphLike) -> Result<Option<Loc>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<BTreeMap<String, ContextVarNode>, GraphError> {
        Ok(self.underlying(analyzer)?.ctx_deps.clone())
    }

    /// Returns a vector of variable dependencies for this context
    pub fn add_ctx_dep(
        &self,
        dep: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        tracing::trace!("Adding ctx dependency: {}", dep.display_name(analyzer)?);
        if dep.is_symbolic(analyzer)? {
            let dep_name = dep.name(analyzer)?;
            let underlying = self.underlying_mut(analyzer)?;
            underlying.ctx_deps.insert(dep_name, dep);
        }
        Ok(())
    }

    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.ret.push((ret_stmt_loc, ret));
        Ok(())
    }

    pub fn return_nodes(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        Ok(self.underlying(analyzer)?.ret.clone())
    }

    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }

    pub fn deps_dag(&self, g: &impl GraphLike) -> Result<(), GraphError> {
        let deps = self.ctx_deps(g)?;
        #[derive(Debug, Copy, Clone)]
        pub enum DepEdge {
            Lhs,
            Rhs,
        }

        let mut gr: petgraph::Graph<NodeIdx, DepEdge, petgraph::Directed, usize> =
            petgraph::Graph::default();
        deps.iter().try_for_each(|(_, dep)| {
            let mapping = dep.graph_dependent_on(g)?;
            mapping.into_iter().for_each(|(k, tmp)| {
                let top = gr.add_node(k.into());
                let lhs = gr.add_node(tmp.lhs.into());
                gr.add_edge(top, lhs, DepEdge::Lhs);
                if let Some(rhs) = tmp.rhs {
                    let rhs = gr.add_node(rhs.into());
                    gr.add_edge(top, rhs, DepEdge::Rhs);
                }
            });
            Ok(())
        })?;

        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());
        let nodes_and_edges_str = format!(
            "{:?}",
            Dot::with_attr_getters(
                &gr,
                &[
                    petgraph::dot::Config::GraphContentOnly,
                    petgraph::dot::Config::NodeNoLabel,
                    petgraph::dot::Config::EdgeNoLabel
                ],
                &|_graph, edge_ref| {
                    let e = edge_ref.weight();
                    format!("label = \"{e:?}\"")
                },
                &|_graph, (idx, node_ref)| {
                    let inner = match g.node(*node_ref) {
                        Node::ContextVar(cvar) => {
                            let range_str = if let Some(r) = cvar.ty.range(g).unwrap() {
                                r.as_dot_str(g)
                                // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(g).unwrap(),
                                range_str
                            )
                        }
                        _ => as_dot_str(idx, g),
                    };
                    format!(
                        "label = \"{}\", color = \"{}\"",
                        inner.replace('\"', "\'"),
                        g.node(*node_ref).dot_str_color()
                    )
                }
            )
        );
        dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        let dot_str = dot_str.join("\n");

        println!("{dot_str}");
        use std::env::temp_dir;
        use std::fs;
        use std::io::Write;
        use std::process::Command;
        let mut dir = temp_dir();
        let file_name = "dot.dot";
        dir.push(file_name);

        let mut file = fs::File::create(dir.clone()).unwrap();
        file.write_all(dot_str.as_bytes()).unwrap();
        Command::new("dot")
            .arg("-Tsvg")
            .arg(dir)
            .arg("-o")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
        Command::new("open")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
        Ok(())
    }
}

impl From<ContextNode> for NodeIdx {
    fn from(val: ContextNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}
