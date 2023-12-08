use crate::{
    nodes::{ FunctionParamNode, ContextVarNode, Context, FunctionNode, KilledKind },
    GraphError, Node
};

use shared::{AsDotStr, NodeIdx, AnalyzerLike, GraphLike};

use solang_parser::pt::Loc;
use std::collections::BTreeMap;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    pub fn join(
        &self,
        _func: FunctionNode,
        _mapping: &BTreeMap<ContextVarNode, FunctionParamNode>,
        _analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        todo!("Joining not supported yet");
    }

    /// Gets the total context width
    pub fn total_width(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<usize, GraphError> {
        self.first_ancestor(analyzer)?
            .number_of_live_edges(analyzer)
    }

    /// Gets the total context depth
    pub fn depth(&self, analyzer: &impl GraphLike) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).unwrap().path.clone()
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

    /// Returns an option to where the context was killed
    pub fn killed_loc(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<(Loc, KilledKind)>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Add a return node to the context
    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?
            .ret
            .push((ret_stmt_loc, Some(ret)));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    /// Add an empty/placeholder return to the context
    pub fn add_empty_return(
        &self,
        ret_stmt_loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?
            .ret
            .push((ret_stmt_loc, None));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    /// Propogate that this context has ended up the context graph
    pub fn propogate_end(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying = &mut self.underlying_mut(analyzer)?;
        let curr_live = underlying.number_of_live_edges;
        underlying.number_of_live_edges = 0;
        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            let live_edges = &mut parent.underlying_mut(analyzer)?.number_of_live_edges;
            *live_edges = live_edges.saturating_sub(1 + curr_live);
            parent.propogate_end(analyzer)?;
        }
        Ok(())
    }

    /// Gets the return nodes for this context
    pub fn return_nodes(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        let rets = &self.underlying(analyzer)?.ret.clone();
        let all_good = rets.iter().all(|(_, node)| node.is_some());
        if all_good {
            Ok(rets
                .iter()
                .map(|(loc, node)| (*loc, node.unwrap()))
                .collect())
        } else {
            Ok(vec![])
        }
    }

    /// Returns a string for dot-string things
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