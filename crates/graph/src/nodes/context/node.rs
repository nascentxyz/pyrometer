use crate::{
    nodes::{Concrete, Context, ContextVarNode, KilledKind},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, GraphBackend, Node,
};

use shared::{GraphError, NodeIdx, RangeArena};

use solang_parser::pt::Loc;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    pub fn add_gas_cost(
        &self,
        analyzer: &mut impl GraphBackend,
        cost: u64,
    ) -> Result<(), GraphError> {
        self.associated_fn(analyzer)?.add_gas_cost(analyzer, cost)
    }

    /// Gets the total context width
    pub fn total_width(&self, analyzer: &mut impl AnalyzerBackend) -> Result<usize, GraphError> {
        self.first_ancestor(analyzer)?
            .number_of_live_edges(analyzer)
    }

    /// Gets the total context depth
    pub fn depth(&self, analyzer: &impl GraphBackend) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphBackend) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl AnalyzerBackend<Node = Node>,
    ) -> Result<&'a mut Context, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Context(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Context, GraphError> {
        match analyzer.node(*self) {
            Node::Context(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<(Loc, KilledKind)>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Add a return node to the context
    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.ret.push((ret_stmt_loc, ret));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    /// Propogate that this context has ended up the context graph
    pub fn propogate_end(&self, analyzer: &mut impl AnalyzerBackend) -> Result<(), GraphError> {
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

    /// Propogate that this context has ended up the context graph
    pub fn propogate_applied(
        &self,
        applied: FunctionNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let underlying = self.underlying_mut(analyzer)?;
        if !underlying.applies.contains(&applied) {
            underlying.applies.push(applied);
        }
        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            parent.propogate_applied(applied, analyzer)?;
        }
        Ok(())
    }

    /// Gets the return nodes for this context
    pub fn return_nodes(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        Ok(self.underlying(analyzer)?.ret.clone())
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
