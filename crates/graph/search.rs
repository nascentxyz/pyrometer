
impl<T> Search for T where T: GraphLike {}


/// A trait for searching through a graph
pub trait Search: GraphLike {
    /// Given a start node, search for an ancestor via an edge type
    fn search_for_ancestor(&self, start: NodeIdx, edge_ty: &Edge) -> Option<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Outgoing);
        if let Some(edge) = edges.clone().find(|edge| edge.weight() == edge_ty) {
            Some(edge.target())
        } else {
            edges
                .map(|edge| edge.target())
                .filter_map(|node| self.search_for_ancestor(node, edge_ty))
                .take(1)
                .next()
        }
    }

    /// Given a start node, search for an ancestor via a set of edge types
    fn search_for_ancestor_multi(&self, start: NodeIdx, edge_tys: &[Edge]) -> Option<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Outgoing);
        if let Some(edge) = edges.clone().find(|edge| edge_tys.contains(edge.weight())) {
            Some(edge.target())
        } else {
            edges
                .map(|edge| edge.target())
                .filter_map(|node| self.search_for_ancestor_multi(node, edge_tys))
                .take(1)
                .next()
        }
    }
    /// Finds any child nodes that have some edge `edge_ty` incoming. Builds up a set of these
    ///
    /// i.e.: a -my_edge-> b -other_edge-> c -my_edge-> d
    ///
    /// This function would build a set { b, d } if we are looking for `my_edge` and start at a.
    fn search_children(&self, start: NodeIdx, edge_ty: &Edge) -> BTreeSet<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .flat_map(|edge| self.search_children(edge.source(), edge_ty))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn find_child_exclude_via(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
        exclude_edges: &[Edge],
        find_fn: &impl Fn(NodeIdx, &Self) -> Option<NodeIdx>,
    ) -> Option<NodeIdx> {
        let edges = self
            .graph()
            .edges_directed(start, Direction::Incoming)
            .filter(|edge| !exclude_edges.contains(edge.weight()));
        if let Some(node) = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .find(|node| find_fn(*node, self).is_some())
        {
            Some(node)
        } else {
            edges
                .clone()
                .map(|edge| edge.source())
                .find_map(|node| self.find_child_exclude_via(node, edge_ty, exclude_edges, find_fn))
        }
    }

    fn search_children_exclude_via(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
        exclude_edges: &[Edge],
    ) -> BTreeSet<NodeIdx> {
        let edges = self
            .graph()
            .edges_directed(start, Direction::Incoming)
            .filter(|edge| !exclude_edges.contains(edge.weight()));
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .flat_map(|edge| {
                    self.search_children_exclude_via(edge.source(), edge_ty, exclude_edges)
                })
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn search_children_include_via(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
        include_edges: &[Edge],
    ) -> BTreeSet<NodeIdx> {
        let mut edges: Vec<_> = self
            .graph()
            .edges_directed(start, Direction::Incoming)
            .collect();
        edges = edges
            .into_iter()
            .filter(|edge| include_edges.contains(edge.weight()))
            .collect::<Vec<_>>();
        let mut this_children: BTreeSet<NodeIdx> = edges
            .iter()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .clone()
                .iter()
                .flat_map(|edge| {
                    self.search_children_include_via(edge.source(), edge_ty, include_edges)
                })
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn search_children_depth(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
        max_depth: usize,
        curr_depth: usize,
    ) -> BTreeSet<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        if curr_depth < max_depth {
            this_children.extend(
                edges
                    .flat_map(|edge| {
                        self.search_children_depth(
                            edge.source(),
                            edge_ty,
                            max_depth,
                            curr_depth + 1,
                        )
                    })
                    .collect::<BTreeSet<NodeIdx>>(),
            );
        }
        this_children
    }

    /// Gets all children recursively
    fn children(&self, start: NodeIdx) -> BTreeSet<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> =
            edges.clone().map(|edge| edge.source()).collect();

        this_children.extend(
            edges
                .flat_map(|edge| self.children(edge.source()))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    /// Gets all children edges recursively
    fn children_edges(
        &self,
        start: NodeIdx,
    ) -> BTreeSet<(NodeIdx, NodeIdx, Edge, EdgeIndex<usize>)> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children_edges: BTreeSet<(NodeIdx, NodeIdx, Edge, EdgeIndex<usize>)> = edges
            .clone()
            .map(|edge| (edge.source(), edge.target(), *edge.weight(), edge.id()))
            .collect();

        this_children_edges.extend(
            edges
                .flat_map(|edge| self.children_edges(edge.source()))
                .collect::<BTreeSet<(NodeIdx, NodeIdx, Edge, EdgeIndex<usize>)>>(),
        );
        this_children_edges
    }

    /// Finds any child nodes that have some edge `edge_ty` incoming. Builds up a mapping of these
    ///
    /// i.e.: a -my_edge-> b -other_edge-> c -my_edge-> d
    ///
    /// This function would build a map { a: [b], c: [d] } if we are looking for `my_edge` and start at a.
    fn nodes_with_children(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
    ) -> Option<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut map: BTreeMap<NodeIdx, BTreeSet<NodeIdx>> = Default::default();

        let this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        if !this_children.is_empty() {
            map.insert(start, this_children);
        }
        map.extend(
            edges
                .filter_map(|edge| self.nodes_with_children(edge.source(), edge_ty))
                .flatten()
                .collect::<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>>(),
        );
        if map.is_empty() {
            None
        } else {
            Some(map)
        }
    }
}