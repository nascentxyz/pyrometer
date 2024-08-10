use crate::nodes::Context;
use crate::{
    nodes::{CallFork, ContextNode, FunctionNode, KilledKind},
    AnalyzerBackend, GraphBackend, Node,
};
use shared::GraphError;

use solang_parser::pt::Loc;

use super::underlying::SubContextKind;

impl ContextNode {
    /// Query whether this context has a parent
    pub fn has_parent(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.parent_ctx().is_some())
    }

    /// Gets the first ancestor of this context
    pub fn first_ancestor(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ContextNode, GraphError> {
        if let Some(first_ancestor) = self.underlying(analyzer)?.cache.first_ancestor {
            Ok(first_ancestor)
        } else if let Some(parent) = self.underlying(analyzer)?.parent_ctx() {
            let first = parent.first_ancestor(analyzer)?;
            self.underlying_mut(analyzer)?.cache.first_ancestor = Some(first);
            Ok(first)
        } else {
            Ok(*self)
        }
    }

    /// Gets the subcontexts of this context
    pub fn subcontexts(&self, analyzer: &impl GraphBackend) -> Vec<ContextNode> {
        let underlying = self.underlying(analyzer).unwrap();
        match underlying.child {
            Some(CallFork::Call(c)) => vec![c],
            Some(CallFork::Fork(w1, w2)) => vec![w1, w2],
            None => vec![],
        }
    }

    /// Get the first ancestor context that is in the same function
    pub fn ancestor_in_fn(
        &self,
        analyzer: &impl GraphBackend,
        associated_fn: FunctionNode,
    ) -> Result<Option<ContextNode>, GraphError> {
        if let Some(ret) = self.underlying(analyzer)?.returning_ctx() {
            if ret.associated_fn(analyzer)? == associated_fn {
                return Ok(Some(ret));
            }
        }

        if let Some(parent) = self.underlying(analyzer)?.parent_ctx() {
            if parent.associated_fn(analyzer)? == associated_fn {
                Ok(Some(parent))
            } else if let Some(mod_state) = &parent.underlying(analyzer)?.modifier_state {
                if mod_state.parent_fn == associated_fn {
                    Ok(Some(parent))
                } else {
                    parent.ancestor_in_fn(analyzer, associated_fn)
                }
            } else {
                parent.ancestor_in_fn(analyzer, associated_fn)
            }
        } else {
            Ok(None)
        }
    }

    /// Returns all forks associated with the context
    pub fn calls(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
        let descendents = self.descendents(analyzer)?;
        Ok(descendents
            .into_iter()
            .filter_map(|c| c.maybe_call())
            .collect())
    }

    /// Returns tail contexts associated with the context
    pub fn live_edges(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.live_edges(analyzer)?;
                    if call_edges.is_empty() && !call.is_ended(analyzer)? {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.live_edges(analyzer)?;
                    if fork_edges.is_empty() && !w1.is_ended(analyzer)? {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.live_edges(analyzer)?;
                    if fork_edges.is_empty() && !w2.is_ended(analyzer)? {
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

    /// Gets all reverted descendents
    pub fn reverted_edges(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.reverted_edges(analyzer)?;
                    if call_edges.is_empty() && call.is_killed(analyzer)? {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.reverted_edges(analyzer)?;
                    if fork_edges.is_empty() && w1.is_killed(analyzer)? {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.reverted_edges(analyzer)?;
                    if fork_edges.is_empty() && w2.is_killed(analyzer)? {
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

    /// Gets all successful descendents
    pub fn successful_edges(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.successful_edges(analyzer)?;
                    let is_graceful_ended = call.is_graceful_ended(analyzer)?;
                    let bad_killed = call.is_killed(analyzer)? && !is_graceful_ended;
                    if call_edges.is_empty() && !bad_killed {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.successful_edges(analyzer)?;
                    let is_graceful_ended = w1.is_graceful_ended(analyzer)?;
                    let bad_killed = w1.is_killed(analyzer)? && !is_graceful_ended;
                    if fork_edges.is_empty() && !bad_killed {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.successful_edges(analyzer)?;

                    let is_graceful_ended = w2.is_graceful_ended(analyzer)?;
                    let bad_killed = w2.is_killed(analyzer)? && !is_graceful_ended;

                    if fork_edges.is_empty() && !bad_killed {
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

    /// Returns the current number of live edges
    pub fn number_of_live_edges(&self, analyzer: &impl GraphBackend) -> Result<usize, GraphError> {
        Ok(self.underlying(analyzer)?.number_of_live_edges)
    }

    /// Returns tail contexts associated with the context
    pub fn all_edges(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
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

    /// Gets all descendents recursively
    pub fn descendents(&self, analyzer: &impl GraphBackend) -> Result<Vec<CallFork>, GraphError> {
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

    /// Gets all descendents as context nodes recursively
    pub fn family_tree(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextNode>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut tree = vec![];
            match child {
                CallFork::Call(c) => {
                    tree.push(c);
                    tree.extend(c.family_tree(analyzer)?)
                }
                CallFork::Fork(w1, w2) => {
                    tree.push(w1);
                    tree.push(w2);
                    tree.extend(w1.family_tree(analyzer)?);
                    tree.extend(w2.family_tree(analyzer)?);
                }
            }
            Ok(tree)
        } else {
            Ok(vec![])
        }
    }

    /// Adds a fork to the context
    pub fn set_child_fork(
        &self,
        w1: ContextNode,
        w2: ContextNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        assert!(matches!(analyzer.node(w1), Node::Context(_)));
        assert!(matches!(analyzer.node(w2), Node::Context(_)));
        assert!(*self != w1 && *self != w2, "Tried to set child to self");
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
                "This is a bug. Tried to redefine a child context, parent:\n{}, current child:\n{},\nnew child: Fork({}, {})",
                self.path(analyzer),
                child_str,
                w1.path(analyzer),
                w2.path(analyzer),
            )))
        } else {
            Ok(())
        }
    }

    pub fn set_apply_forks(
        &self,
        loc: Loc,
        end_worlds: Vec<ContextNode>,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Vec<ContextNode>, GraphError> {
        // if we have 4 worlds we need to represent
        // we need to construct a tree like this
        //          a
        //          |
        //     |----------|
        //     a1         a2
        //     |          |
        // |------|    |------|
        // a3     a4   a5     a6
        //
        // each fork adds 1 world

        let _edges = self.all_edges(analyzer)?;
        let mut stack = std::collections::VecDeque::new();
        stack.push_front(*self);

        for _ in 0..end_worlds.len().saturating_sub(1) {
            let curr = stack.pop_front().unwrap();

            let left_subctx = Context::add_subctx(
                SubContextKind::Fork {
                    parent_ctx: curr,
                    true_side: true,
                },
                loc,
                analyzer,
                None,
                curr.contract_id(analyzer)?,
            )?;
            let right_subctx = Context::add_subctx(
                SubContextKind::Fork {
                    parent_ctx: curr,
                    true_side: false,
                },
                loc,
                analyzer,
                None,
                curr.contract_id(analyzer)?,
            )?;
            curr.set_child_fork(left_subctx, right_subctx, analyzer)?;

            stack.push_back(left_subctx);
            stack.push_back(right_subctx);
        }

        self.all_edges(analyzer)
    }

    /// Adds a child to the context
    pub fn set_child_call(
        &self,
        call: ContextNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        assert!(matches!(analyzer.node(call), Node::Context(_)));
        assert!(*self != call, "Tried to set child to self");
        let context = self.underlying_mut(analyzer)?;
        if !context.set_child_call(call) {
            let child_str = match context.child {
                Some(CallFork::Fork(w1, w2)) => {
                    format!("fork {{ {}, {} }}", w1.path(analyzer), w2.path(analyzer))
                }
                Some(CallFork::Call(call)) => format!("call {{ {} }}", call.path(analyzer)),
                None => unreachable!(),
            };
            tracing::trace!("Error setting child as a call");
            Err(GraphError::ChildRedefinition(format!(
                "This is a bug. Tried to redefine a child context, parent: {}, current child: {}, new child: {}",
                self.path(analyzer),
                child_str,
                call.path(analyzer)
            )
            ))
        } else {
            Ok(())
        }
    }

    /// Removes the child of this context
    pub fn delete_child(&self, analyzer: &mut impl AnalyzerBackend) -> Result<(), GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            match child {
                CallFork::Fork(w1, w2) => {
                    w1.propogate_end(analyzer)?;
                    w2.propogate_end(analyzer)?;
                }
                CallFork::Call(c) => {
                    c.propogate_end(analyzer)?;
                }
            }
        }
        let context = self.underlying_mut(analyzer)?;
        context.delete_child();
        Ok(())
    }

    /// Kills the context by denoting it as killed. Recurses up the contexts and kills
    /// parent contexts if all subcontexts of that context are killed
    pub fn kill(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        kill_loc: Loc,
        kill_kind: KilledKind,
    ) -> Result<(), GraphError> {
        tracing::trace!("killing: {}, {kill_kind:?}", self.path(analyzer));
        if let Some(child) = self.underlying(analyzer)?.child {
            match child {
                CallFork::Call(call) => {
                    if !call.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }
                    call.kill(analyzer, kill_loc, kill_kind)?;
                }
                CallFork::Fork(w1, w2) => {
                    if !w1.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }

                    if !w2.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }

                    w1.kill(analyzer, kill_loc, kill_kind)?;
                    w2.kill(analyzer, kill_loc, kill_kind)?;
                }
            }
        }

        let context = self.underlying_mut(analyzer)?;
        let parent = context.parent_ctx();
        if context.killed.is_none() {
            context.killed = Some((kill_loc, kill_kind));
        }

        if let Some(parent_ctx) = parent {
            parent_ctx.end_if_all_forks_ended(analyzer, kill_loc, kill_kind)?;
        }

        self.propogate_end(analyzer)?;

        Ok(())
    }

    /// Kills if and only if all subcontexts are killed
    pub fn end_if_all_forks_ended(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        kill_loc: Loc,
        kill_kind: KilledKind,
    ) -> Result<(), GraphError> {
        let all_edges = self.all_edges(analyzer)?;
        let reverted_edges = self.reverted_edges(analyzer)?;
        if reverted_edges.len() == all_edges.len() {
            tracing::trace!("killing recursively: {}", self.path(analyzer));
            let context = self.underlying_mut(analyzer)?;
            if context.ret.is_empty() {
                if context.killed.is_none() {
                    context.killed = Some((kill_loc, kill_kind));
                }
                if let Some(parent_ctx) = context.parent_ctx() {
                    parent_ctx.end_if_all_forks_ended(analyzer, kill_loc, kill_kind)?;
                }
            }
        }
        Ok(())
    }

    /// Gets parent list
    pub fn parent_list(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextNode>, GraphError> {
        let context = self.underlying(analyzer)?;
        let mut parents = vec![];
        if let Some(parent_ctx) = context.parent_ctx() {
            parents.push(parent_ctx);
            parents.extend(parent_ctx.parent_list(analyzer)?);
        }
        Ok(parents)
    }

    /// Gets the first context in the lineage
    pub fn genesis(&self, analyzer: &impl GraphBackend) -> Result<ContextNode, GraphError> {
        let context = self.underlying(analyzer)?;
        if let Some(parent_ctx) = context.parent_ctx() {
            parent_ctx.genesis(analyzer)
        } else {
            Ok(*self)
        }
    }

    /// Gets all calls recursively
    pub fn recursive_calls(
        &self,
        analyzer: &impl GraphBackend,
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
        _analyzer: &impl GraphBackend,
        _entry: bool,
    ) -> Result<Vec<ContextNode>, GraphError> {
        todo!()
    }
}
