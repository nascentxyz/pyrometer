use crate::Analyzer;

use shared::GraphLike;
use graph::{GraphBackend, Node, Edge};

use petgraph::{Graph, Directed};

impl GraphLike for Analyzer {
	type Node = Node;
	type Edge = Edge;
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        &mut self.graph
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        &self.graph
    }
}

impl GraphBackend for Analyzer {}