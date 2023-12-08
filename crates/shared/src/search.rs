use std::collections::{BTreeMap, BTreeSet};

use crate::{GraphLike, NodeIdx};
use petgraph::{graph::*, visit::EdgeRef, Direction};

pub trait Heirarchical {
    fn heirarchical_num(&self) -> usize;
}

impl<T> Search for T
where
    T: GraphLike,
    <T as GraphLike>::Edge: Ord + PartialEq + Heirarchical + Copy,
{
}
/// A trait for searching through a graph
pub trait Search: GraphLike
where
    <Self as GraphLike>::Edge: PartialEq + Heirarchical + Copy,
{
    fn search_for_ancestor(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
    ) -> Option<NodeIdx> {
        tracing::trace!("searching for ancestor");
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

    fn search_for_ancestor_multi(
        &self,
        start: NodeIdx,
        edge_tys: &[<Self as GraphLike>::Edge],
    ) -> Option<NodeIdx> {
        tracing::trace!("searching for ancestor_multi");
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

    fn search_children_same_heirarchy(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("search_children_same_heirarchy");
        let num = edge_ty.heirarchical_num();
        let edges = self
            .graph()
            .edges_directed(start, Direction::Incoming)
            .filter(|e| e.weight().heirarchical_num() == num);
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
                .flat_map(|edge| self.search_children_same_heirarchy(edge.source(), edge_ty))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    /// Finds any child nodes that have some edge `edge_ty` incoming. Builds up a set of these
    ///
    /// i.e.: a -my_edge-> b -other_edge-> c -my_edge-> d
    ///
    /// This function would build a set { b, d } if we are looking for `my_edge` and start at a.
    fn search_children(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("search_children");
        let mut seen = Default::default();
        self.search_children_prevent_cycle(start, edge_ty, &mut seen)
    }

    fn search_children_prevent_cycle(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    if !seen.contains(&edge.source()) {
                        Some(edge.source())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .flat_map(|edge| self.search_children_prevent_cycle(edge.source(), edge_ty, seen))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn find_child_exclude_via(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        exclude_edges: &[<Self as GraphLike>::Edge],
        find_fn: &impl Fn(NodeIdx, &Self) -> Option<NodeIdx>,
    ) -> Option<NodeIdx> {
        tracing::trace!("find_child_exclude_via");
        let mut seen = Default::default();
        self.find_child_exclude_via_prevent_cycle(start, edge_ty, exclude_edges, find_fn, &mut seen)
    }

    fn find_child_exclude_via_prevent_cycle(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        exclude_edges: &[<Self as GraphLike>::Edge],
        find_fn: &impl Fn(NodeIdx, &Self) -> Option<NodeIdx>,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> Option<NodeIdx> {
        if seen.contains(&start) {
            return None;
        } else {
            seen.insert(start);
        }

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
        edge_ty: &<Self as GraphLike>::Edge,
        exclude_edges: &[<Self as GraphLike>::Edge],
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("search_children_exclude_via");
        let mut seen = Default::default();
        self.search_children_exclude_via_prevent_cycle(start, edge_ty, exclude_edges, &mut seen)
    }

    fn search_children_exclude_via_prevent_cycle(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        exclude_edges: &[<Self as GraphLike>::Edge],
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

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
        seen.insert(start);

        this_children.extend(
            edges
                .flat_map(|edge| {
                    self.search_children_exclude_via_prevent_cycle(
                        edge.source(),
                        edge_ty,
                        exclude_edges,
                        seen,
                    )
                })
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn search_children_include_via(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        include_edges: &[<Self as GraphLike>::Edge],
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("search_children_include_via");
        let mut seen = Default::default();
        self.search_children_include_via_prevent_cycle(start, edge_ty, include_edges, &mut seen)
    }

    fn search_children_include_via_prevent_cycle(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        include_edges: &[<Self as GraphLike>::Edge],
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

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
                    self.search_children_include_via_prevent_cycle(
                        edge.source(),
                        edge_ty,
                        include_edges,
                        seen,
                    )
                })
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    fn search_children_depth(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        max_depth: usize,
        curr_depth: usize,
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("search_children_depth");
        let mut seen = Default::default();
        self.search_children_depth_prevent_cylce(start, edge_ty, max_depth, curr_depth, &mut seen)
    }

    fn search_children_depth_prevent_cylce(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        max_depth: usize,
        curr_depth: usize,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

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
                        self.search_children_depth_prevent_cylce(
                            edge.source(),
                            edge_ty,
                            max_depth,
                            curr_depth + 1,
                            seen,
                        )
                    })
                    .collect::<BTreeSet<NodeIdx>>(),
            );
        }
        this_children
    }

    /// Gets all children recursively, removing nodes that are connected via an excluded edge
    fn children_exclude(
        &self,
        start: NodeIdx,
        max_depth: usize,
        exclude_edges: &[<Self as GraphLike>::Edge],
    ) -> BTreeSet<NodeIdx> {
        tracing::trace!("children");
        let mut seen = Default::default();
        self.children_exclude_prevent_cycle(start, 0, max_depth, exclude_edges, &mut seen)
    }

    /// Gets all children recursively up to a certain depth
    fn children_exclude_prevent_cycle(
        &self,
        start: NodeIdx,
        curr_depth: usize,
        max_depth: usize,
        exclude_edges: &[<Self as GraphLike>::Edge],
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if curr_depth > max_depth {
            return Default::default();
        }

        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if !exclude_edges.contains(edge.weight()) {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .flat_map(|edge| {
                    self.children_exclude_prevent_cycle(
                        edge.source(),
                        curr_depth + 1,
                        max_depth,
                        exclude_edges,
                        seen,
                    )
                })
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    /// Gets all children recursively
    fn children(&self, start: NodeIdx) -> BTreeSet<NodeIdx> {
        tracing::trace!("children");
        let mut seen = Default::default();
        self.children_prevent_cycle(start, &mut seen)
    }

    /// Gets all children recursively
    fn children_prevent_cycle(
        &self,
        start: NodeIdx,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<NodeIdx> {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> =
            edges.clone().map(|edge| edge.source()).collect();

        this_children.extend(
            edges
                .flat_map(|edge| self.children_prevent_cycle(edge.source(), seen))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    /// Gets all children edges recursively
    fn edges_for_nodes(
        &self,
        nodes: &BTreeSet<NodeIdx>,
    ) -> BTreeSet<(
        NodeIdx,
        NodeIdx,
        <Self as GraphLike>::Edge,
        EdgeIndex<usize>,
    )>
    where
        <Self as GraphLike>::Edge: Ord,
    {
        tracing::trace!("children_edges");

        nodes
            .iter()
            .flat_map(|node| {
                self.graph()
                    .edges_directed(*node, Direction::Incoming)
                    .map(|edge| (edge.source(), edge.target(), *edge.weight(), edge.id()))
                    .collect::<BTreeSet<(
                        NodeIdx,
                        NodeIdx,
                        <Self as GraphLike>::Edge,
                        EdgeIndex<usize>,
                    )>>()
            })
            .collect()
    }

    /// Gets all children edges recursively
    fn children_edges(
        &self,
        start: NodeIdx,
    ) -> BTreeSet<(
        NodeIdx,
        NodeIdx,
        <Self as GraphLike>::Edge,
        EdgeIndex<usize>,
    )>
    where
        <Self as GraphLike>::Edge: Ord,
    {
        tracing::trace!("children_edges");
        let mut seen = Default::default();
        self.children_edges_prevent_cycle(start, &mut seen)
    }

    fn children_edges_prevent_cycle(
        &self,
        start: NodeIdx,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> BTreeSet<(
        NodeIdx,
        NodeIdx,
        <Self as GraphLike>::Edge,
        EdgeIndex<usize>,
    )>
    where
        <Self as GraphLike>::Edge: Ord,
    {
        if seen.contains(&start) {
            return Default::default();
        } else {
            seen.insert(start);
        }

        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children_edges: BTreeSet<(
            NodeIdx,
            NodeIdx,
            <Self as GraphLike>::Edge,
            EdgeIndex<usize>,
        )> = edges
            .clone()
            .map(|edge| (edge.source(), edge.target(), *edge.weight(), edge.id()))
            .collect();

        this_children_edges.extend(
            edges
                .flat_map(|edge| self.children_edges_prevent_cycle(edge.source(), seen))
                .collect::<BTreeSet<(
                    NodeIdx,
                    NodeIdx,
                    <Self as GraphLike>::Edge,
                    EdgeIndex<usize>,
                )>>(),
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
        edge_ty: &<Self as GraphLike>::Edge,
    ) -> Option<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>> {
        tracing::trace!("nodes_with_children");
        let mut seen = Default::default();
        self.nodes_with_children_prevent_cycles(start, edge_ty, &mut seen)
    }

    fn nodes_with_children_prevent_cycles(
        &self,
        start: NodeIdx,
        edge_ty: &<Self as GraphLike>::Edge,
        seen: &mut BTreeSet<NodeIdx>,
    ) -> Option<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>> {
        if seen.contains(&start) {
            return None;
        } else {
            seen.insert(start);
        }
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
                .filter_map(|edge| {
                    self.nodes_with_children_prevent_cycles(edge.source(), edge_ty, seen)
                })
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
