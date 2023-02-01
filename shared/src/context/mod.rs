use crate::{Node, NodeIdx, Edge};
use crate::analyzer::{AnalyzerLike, Search};
use crate::nodes::FunctionNode;
use solang_parser::pt::Loc;
use std::collections::HashMap;


mod var;
pub use var::*;

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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Context {
    /// The function associated with this context
    pub parent_fn: FunctionNode,
    /// An optional parent context (i.e. this context is a fork or subcontext of another previous context)
    pub parent_ctx: Option<ContextNode>,
    /// Variables whose bounds are required to be met for this context fork to exist. i.e. a conditional operator
    /// like an if statement
    pub ctx_deps: HashMap<String, ContextVarNode>,
    /// A string that represents the path taken from the root context (i.e. `fn_entry.fork.1`)
    pub path: String,
    /// Denotes whether this context was killed by an unsatisfiable require, assert, etc. statement
    pub killed: Option<Loc>,
    /// Denotes whether this context is a fork of another context
    pub is_fork: bool,
    /// A vector of forks of this context
    pub forks: Vec<ContextNode>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Option<(Loc, ContextVarNode)>,
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
            forks: vec![],
            ret: None,
            loc,
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        parent_ctx: ContextNode,
        loc: Loc,
        is_fork: bool,
        analyzer: &impl AnalyzerLike,
    ) -> Self {
        Context {
            parent_fn: parent_ctx.underlying(analyzer).parent_fn.clone(),
            parent_ctx: Some(parent_ctx),
            path: format!(
                "{}.{}",
                parent_ctx.underlying(analyzer).path,
                if is_fork {
                    format!("fork.{}", parent_ctx.underlying(analyzer).forks.len())
                } else {
                    "child".to_string()
                }
            ),
            is_fork,
            ctx_deps: parent_ctx.underlying(analyzer).ctx_deps.clone(),
            killed: None,
            forks: vec![],
            tmp_var_ctr: 0,
            ret: None,
            loc,
        }
    }

    /// Add a fork to this context
    pub fn add_fork(&mut self, fork_node: ContextNode) {
        self.forks.push(fork_node);
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);
impl ContextNode {
    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl AnalyzerLike) -> String {
        self.underlying(analyzer).path.clone()
    }

    /// *All* subcontexts (including subcontexts of subcontexts, recursively)
    pub fn subcontexts(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<ContextNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Subcontext))
            .into_iter()
            .map(|idx| ContextNode::from(idx))
            .collect()
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &(impl AnalyzerLike + Search)) -> FunctionNode {
        self.underlying(analyzer).parent_fn
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        self.underlying(analyzer).parent_fn.name(analyzer)
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl AnalyzerLike) -> &'a mut Context {
        match analyzer.node_mut(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Context {
        match analyzer.node(*self) {
            Node::Context(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Context but it was: {:?}",
                e
            ),
        }
    }

    /// Gets a variable by name in the context
    pub fn var_by_name(&self, analyzer: &impl AnalyzerLike, name: &str) -> Option<ContextVarNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
            .into_iter()
            .filter_map(|cvar_node| {
                let cvar_node = ContextVarNode::from(cvar_node);
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

    /// Gets all variables associated with a context
    pub fn vars(&self, analyzer: &impl AnalyzerLike) -> Vec<ContextVarNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
            .into_iter()
            .map(|idx| ContextVarNode::from(idx))
            .collect()
    }

    /// Gets the latest version of a variable associated with a context
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

    /// Reads the current temporary counter and increments the counter
    pub fn new_tmp(&self, analyzer: &mut impl AnalyzerLike) -> usize {
        let context = self.underlying_mut(analyzer);
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        ret
    }

    /// Returns all forks associated with the context
    pub fn forks(&self, analyzer: &impl AnalyzerLike) -> Vec<Self> {
        let context = self.underlying(analyzer);
        context.forks.clone()
    }

    /// Returns all *live* forks associated with the context
    pub fn live_forks(&self, analyzer: &impl AnalyzerLike) -> Vec<Self> {
        let context = self.underlying(analyzer);
        context
            .forks
            .iter()
            .filter(|fork_ctx| !fork_ctx.is_killed(analyzer))
            .cloned()
            .collect()
    }

    /// Adds a fork to the context
    pub fn add_fork(&self, fork: ContextNode, analyzer: &mut impl AnalyzerLike) {
        let context = self.underlying_mut(analyzer);
        context.add_fork(fork);
    }

    /// Kills the context by denoting it as killed. Recurses up the contexts and kills
    /// parent contexts if all subcontexts of that context are killed
    pub fn kill(&self, analyzer: &mut impl AnalyzerLike, kill_loc: Loc) {
        let context = self.underlying_mut(analyzer);
        context.killed = Some(kill_loc);
        if let Some(parent_ctx) = context.parent_ctx {
            parent_ctx.kill_if_all_forks_killed(analyzer, kill_loc);
        }
    }

    /// Kills if and only if all subcontexts are killed
    pub fn kill_if_all_forks_killed(&self, analyzer: &mut impl AnalyzerLike, kill_loc: Loc) {
        let context = self.underlying(analyzer);
        if context
            .forks
            .iter()
            .all(|fork_ctx| fork_ctx.is_killed(analyzer))
        {
            let context = self.underlying_mut(analyzer);
            context.killed = Some(kill_loc);
            if let Some(parent_ctx) = context.parent_ctx {
                parent_ctx.kill_if_all_forks_killed(analyzer, kill_loc);
            }
        }
    }

    /// Returns whether the context is killed
    pub fn is_killed(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).killed.is_some()
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(&self, analyzer: &impl AnalyzerLike) -> Option<Loc> {
        self.underlying(analyzer).killed
    }

    /// Returns a vector of variable dependencies for this context
    pub fn ctx_deps(&self, analyzer: &impl AnalyzerLike) -> HashMap<String, ContextVarNode> {
        self.underlying(analyzer).ctx_deps.clone()
    }

    /// Returns a vector of variable dependencies for this context
    pub fn add_ctx_dep(&self, dep: ContextVarNode, analyzer: &mut impl AnalyzerLike) {
        if !dep.is_const(analyzer) {
            let dep_name = dep.name(analyzer);
            let underlying = self.underlying_mut(analyzer);
            underlying.ctx_deps.insert(dep_name, dep);
        }
    }

    pub fn set_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut impl AnalyzerLike,
    ) {
        self.underlying_mut(analyzer).ret = Some((ret_stmt_loc, ret));
    }

    pub fn return_node(&self, analyzer: &impl AnalyzerLike) -> Option<(Loc, ContextVarNode)> {
        self.underlying(analyzer).ret
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