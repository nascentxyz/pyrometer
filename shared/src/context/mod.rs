use crate::analyzer::GraphError;
use crate::analyzer::{AnalyzerLike, GraphLike, Search};
use crate::nodes::FunctionNode;
use crate::ContractNode;
use crate::StructNode;
use std::collections::BTreeSet;

use crate::{Edge, Node, NodeIdx};
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::Loc;
use std::collections::BTreeMap;
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
    FuncAccess,

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
    pub ctx_deps: HashMap<String, ContextVarNode>,
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
    /// A vector of forks of this context
    pub forks: Vec<ContextNode>,
    /// A vector of children of this context
    pub children: Vec<ContextNode>,
    /// A counter for temporary variables - this lets a context create unique temporary variables
    pub tmp_var_ctr: usize,
    /// The location in source of the context
    pub loc: Loc,
    /// The return node and the return location
    pub ret: Vec<(Loc, ContextVarNode)>,
    /// Range adjustments to occur after the statement finishes. Useful for post in/decrement
    pub post_statement_range_adjs: Vec<(ContextVarNode, Loc, bool)>,
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
            forks: vec![],
            children: vec![],
            ret: vec![],
            loc,
            modifier_state: None,
            post_statement_range_adjs: vec![],
        }
    }

    /// Creates a new subcontext from an existing context
    pub fn new_subctx(
        parent_ctx: ContextNode,
        loc: Loc,
        is_fork: bool,
        fn_call: Option<FunctionNode>,
        fn_ext: bool,
        analyzer: &impl GraphLike,
        modifier_state: Option<ModifierState>,
    ) -> Result<Self, GraphError> {
        let (fn_name, ext_fn_call, fn_call) = if let Some(fn_call) = fn_call {
            if fn_ext {
                (fn_call.name(analyzer)?, Some(fn_call), None)
            } else {
                (fn_call.name(analyzer)?, None, Some(fn_call))
            }
        } else {
            ("anonymous_fn_call".to_string(), None, None)
        };

        Ok(Context {
            parent_fn: parent_ctx.underlying(analyzer)?.parent_fn,
            parent_ctx: Some(parent_ctx),
            path: format!(
                "{}.{}",
                parent_ctx.underlying(analyzer)?.path,
                if is_fork {
                    format!("fork-{}", parent_ctx.underlying(analyzer)?.forks.len())
                } else {
                    format!(
                        "{}-{}",
                        fn_name,
                        parent_ctx.underlying(analyzer)?.children.len()
                    )
                }
            ),
            is_fork,
            fn_call,
            ext_fn_call,
            ctx_deps: parent_ctx.underlying(analyzer)?.ctx_deps.clone(),
            killed: None,
            forks: vec![],
            children: vec![],
            tmp_var_ctr: parent_ctx.underlying(analyzer)?.tmp_var_ctr,
            ret: vec![],
            loc,
            modifier_state,
            post_statement_range_adjs: vec![],
        })
    }

    /// Add a fork to this context
    pub fn add_fork(&mut self, fork_node: ContextNode) {
        self.forks.push(fork_node);
    }

    /// Add a child to this context
    pub fn add_child(&mut self, child_node: ContextNode) {
        self.children.push(child_node);
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
impl ContextNode {
    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    pub fn into_ctx_tree(&self, analyzer: &impl GraphLike) -> CtxTree {
        let forks = self.forks(analyzer).unwrap();
        CtxTree {
            node: *self,
            lhs: if !forks.is_empty() {
                Some(Box::new(forks[0].into_ctx_tree(analyzer)))
            } else {
                None
            },
            rhs: if !forks.is_empty() {
                Some(Box::new(forks[1].into_ctx_tree(analyzer)))
            } else {
                None
            },
        }
    }

    /// *All* subcontexts (including subcontexts of subcontexts, recursively)
    pub fn subcontexts(&self, analyzer: &impl GraphLike) -> Vec<ContextNode> {
        analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Subcontext))
            .into_iter()
            .map(ContextNode::from)
            .collect()
    }

    /// Gets the associated contract for the function for the context
    pub fn associated_contract(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<ContractNode, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer)
            .expect("No associated contract for context"))
    }

    /// Tries to get the associated function for the context
    pub fn maybe_associated_contract(
        &self,
        analyzer: &impl GraphLike,
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
        analyzer: &impl GraphLike,
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
                        panic!("3+ visible functions with the same name. This is invalid solidity")
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
            let inherited_contracts =
                analyzer.search_children(contract.0.into(), &Edge::InheritedContract);
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
                        panic!("3+ visible functions with the same name. This is invalid solidity")
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
            .search_children(source, &Edge::Struct)
            .into_iter()
            .map(StructNode::from)
            .collect::<Vec<_>>()
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &impl GraphLike) -> Result<FunctionNode, GraphError> {
        Ok(self.underlying(analyzer)?.parent_fn)
    }

    /// Checks whether a function is external to the current context
    pub fn is_fn_ext(
        &self,
        fn_node: FunctionNode,
        analyzer: &impl GraphLike,
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
        self.underlying(analyzer)?.parent_fn.name(analyzer)
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
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
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
    }

    pub fn var_by_name_or_recurse(
        &self,
        analyzer: &impl GraphLike,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = analyzer
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
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
            .search_children(self.0.into(), &Edge::Context(ContextEdge::Variable))
            .into_iter()
            .map(ContextVarNode::from)
            .collect()
    }

    /// Gets all variables associated with a context
    pub fn local_vars(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter_map(|edge| {
                if edge.weight() == &Edge::Context(ContextEdge::Variable) {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .map(ContextVarNode::from)
            .collect()
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
    pub fn forks(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        let context = self.underlying(analyzer)?;
        Ok(context.forks.clone())
    }

    /// Returns all *live* forks associated with the context
    pub fn live_forks(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        let context = self.underlying(analyzer)?;
        let mut live = vec![];
        for fork in context.forks.iter() {
            if !fork.is_ended(analyzer)? {
                live.push(*fork);
            }
        }
        Ok(live)
    }

    /// Adds a fork to the context
    pub fn add_fork(
        &self,
        fork: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        context.add_fork(fork);
        Ok(())
    }

    /// Adds a child to the context
    pub fn add_child(
        &self,
        child: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let context = self.underlying_mut(analyzer)?;
        context.add_child(child);
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
        context.killed = Some(kill_loc);
        if let Some(parent_ctx) = context.parent_ctx {
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
        if self.live_forks(analyzer)?.is_empty() {
            let context = self.underlying_mut(analyzer)?;
            context.killed = Some(kill_loc);
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

    /// Gets all terminal children
    pub fn terminal_child_list(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        let context = self.underlying(analyzer)?;
        if context.forks.is_empty() {
            Ok(vec![*self])
        } else {
            let mut forks = vec![];

            for fork in context.forks.clone().into_iter() {
                forks.extend(fork.terminal_child_list(analyzer)?)
            }
            Ok(forks)
        }
    }

    pub fn returning_child_list(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        let context = self.underlying(analyzer)?;
        if context.children.is_empty() {
            Ok(vec![*self])
        } else {
            let mut children = vec![];

            for child in context.children.clone().into_iter() {
                children.extend(child.returning_child_list(analyzer)?)
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
        Ok(underlying.killed.is_some() || !underlying.ret.is_empty())
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(&self, analyzer: &impl GraphLike) -> Result<Option<Loc>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<HashMap<String, ContextVarNode>, GraphError> {
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
