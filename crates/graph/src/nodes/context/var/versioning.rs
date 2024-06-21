use crate::{
    nodes::{ContextNode, ContextVarNode},
    ContextEdge, Edge, GraphBackend, GraphError,
};

use shared::NodeIdx;

use petgraph::{visit::EdgeRef, Direction};

impl ContextVarNode {
    pub fn latest_version(&self, analyzer: &impl GraphBackend) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn latest_version_less_than(&self, idx: NodeIdx, analyzer: &impl GraphBackend) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            if next.0 <= idx.index() {
                latest = next;
            } else {
                break;
            }
        }
        latest
    }

    pub fn latest_version_in_ctx(
        &self,
        ctx: ContextNode,
        analyzer: &impl GraphBackend,
    ) -> Result<Self, GraphError> {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)?) {
            Ok(cvar.latest_version(analyzer))
        } else {
            Ok(*self)
        }
    }

    pub fn latest_version_in_ctx_less_than(
        &self,
        idx: NodeIdx,
        ctx: ContextNode,
        analyzer: &impl GraphBackend,
    ) -> Result<Self, GraphError> {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)?) {
            Ok(cvar.latest_version_less_than(idx, analyzer))
        } else {
            Ok(*self)
        }
    }

    pub fn global_first_version(&self, analyzer: &impl GraphBackend) -> Self {
        let mut global_first = self.first_version(analyzer);

        let mut stack = vec![global_first];

        while let Some(current_node) = stack.pop() {
            let mut pushed = false;
            if let Some(target_node) = analyzer
                .graph()
                .edges_directed(current_node.0.into(), Direction::Outgoing)
                .filter(|edge| {
                    matches!(
                        edge.weight(),
                        Edge::Context(ContextEdge::InheritedVariable)
                            | Edge::Context(ContextEdge::InputVariable)
                    )
                })
                .map(|edge| ContextVarNode::from(edge.target()))
                .take(1)
                .next()
            {
                global_first = target_node.first_version(analyzer);
                stack.push(global_first);
                pushed = true;
            }

            if !pushed {
                continue;
            }
        }

        global_first
    }

    pub fn first_version(&self, analyzer: &impl GraphBackend) -> Self {
        let mut earlier = *self;
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
        }
        earlier
    }

    pub fn num_versions(&self, analyzer: &impl GraphBackend) -> usize {
        let mut count = 1;
        let mut earlier = self.latest_version(analyzer);
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
            count += 1;
        }
        count
    }

    pub fn curr_version_num(&self, analyzer: &impl GraphBackend) -> usize {
        let mut count = 0;
        let mut earlier = self.first_version(analyzer);
        while let Some(next) = earlier.next_version(analyzer) {
            if next == *self {
                break;
            }
            earlier = next;
            count += 1;
        }
        count
    }

    pub fn global_curr_version_num(&self, analyzer: &impl GraphBackend) -> usize {
        let mut stack = vec![*self];
        let mut total_version_num = 0;

        while let Some(current_node) = stack.pop() {
            total_version_num += current_node.curr_version_num(analyzer);

            let mut pushed = false;
            if let Some(target_node) = analyzer
                .graph()
                .edges_directed(current_node.0.into(), Direction::Outgoing)
                .filter(|edge| {
                    matches!(
                        edge.weight(),
                        Edge::Context(ContextEdge::InheritedVariable)
                            | Edge::Context(ContextEdge::InputVariable)
                    )
                })
                .map(|edge| ContextVarNode::from(edge.target()))
                .take(1)
                .next()
            {
                stack.push(target_node);
                pushed = true;
            }

            if !pushed {
                continue;
            }
        }

        total_version_num
    }

    pub fn all_versions(&self, analyzer: &impl GraphBackend) -> Vec<Self> {
        let mut versions = vec![];
        let mut earlier = self.latest_version(analyzer);
        while let Some(prev) = earlier.previous_version(analyzer) {
            versions.push(prev);
            earlier = prev;
        }
        versions
    }

    pub fn next_version(&self, analyzer: &impl GraphBackend) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.source()))
            .take(1)
            .next()
    }

    pub fn next_version_or_inheriteds(&self, analyzer: &impl GraphBackend) -> Vec<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| {
                Edge::Context(ContextEdge::Prev) == *edge.weight()
                    || Edge::Context(ContextEdge::InheritedVariable) == *edge.weight()
            })
            .map(|edge| ContextVarNode::from(edge.source()))
            .collect()
    }

    pub fn other_is_version(&self, other: &Self, analyzer: &impl GraphBackend) -> bool {
        self.all_versions(analyzer).contains(other)
    }

    pub fn previous_version(&self, analyzer: &impl GraphBackend) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn previous_or_inherited_version(&self, analyzer: &impl GraphBackend) -> Option<Self> {
        if let Some(prev) = self.previous_version(analyzer) {
            Some(prev)
        } else {
            analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| Edge::Context(ContextEdge::InheritedVariable) == *edge.weight())
                .map(|edge| ContextVarNode::from(edge.target()))
                .take(1)
                .next()
        }
    }

    pub fn previous_global_version(&self, analyzer: &impl GraphBackend) -> Option<Self> {
        if let Some(prev) = self.previous_version(analyzer) {
            Some(prev)
        } else if let Some(inherited) = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::InheritedVariable) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
        {
            Some(inherited)
        } else {
            analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| Edge::Context(ContextEdge::InputVariable) == *edge.weight())
                .map(|edge| ContextVarNode::from(edge.target()))
                .take(1)
                .next()
        }
    }
}
