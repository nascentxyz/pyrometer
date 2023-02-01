use crate::context::ContextVarNode;
use petgraph::visit::EdgeRef;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use crate::{FunctionParam, DynBuiltin, Function, FunctionReturn, Builtin, Node, Edge, NodeIdx};

use petgraph::dot::Dot;
use petgraph::{graph::*, Directed, Direction};
use std::collections::HashMap;

pub trait AnalyzerLike: GraphLike {
    type Expr;
    fn builtin_fns(&self) -> &HashMap<String, Function>;
    fn builtin_fn_inputs(&self) -> &HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)>;
    fn builtins(&self) -> &HashMap<Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut HashMap<Builtin, NodeIdx>;
    fn builtin_or_add(&mut self, builtin: Builtin) -> NodeIdx {
        if let Some(idx) = self.builtins().get(&builtin) {
            *idx
        } else {
            let idx = self.add_node(Node::Builtin(builtin.clone()));
            self.builtins_mut().insert(builtin, idx);
            idx
        }
    }
    fn dyn_builtins(&self) -> &HashMap<DynBuiltin, NodeIdx>;
    fn dyn_builtins_mut(&mut self) -> &mut HashMap<DynBuiltin, NodeIdx>;
    fn user_types(&self) -> &HashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    fn parse_expr(&mut self, expr: &Self::Expr) -> NodeIdx;
}

pub trait GraphLike {
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize>;
    fn graph(&self) -> &Graph<Node, Edge, Directed, usize>;

    fn add_node(&mut self, node: impl Into<Node>) -> NodeIdx {
        self.graph_mut().add_node(node.into())
    }

    fn node(&self, node: impl Into<NodeIdx>) -> &Node {
        self.graph()
            .node_weight(node.into())
            .expect("Index not in graph")
    }

    fn node_mut(&mut self, node: impl Into<NodeIdx>) -> &mut Node {
        self.graph_mut()
            .node_weight_mut(node.into())
            .expect("Index not in graph")
    }

    fn add_edge(
        &mut self,
        from_node: impl Into<NodeIdx>,
        to_node: impl Into<NodeIdx>,
        edge: impl Into<Edge>,
    ) {
        self.graph_mut()
            .add_edge(from_node.into(), to_node.into(), edge.into());
    }

    fn dot_str(&self) -> String {
        format!("{:?}", Dot::new(self.graph()))
    }

    fn dot_str_no_tmps(&self) -> String {
        let new_graph = self.graph().filter_map(
            |_idx, node| match node {
                Node::ContextVar(cvar) => {
                    if cvar.tmp_of.is_some() {
                        None
                    } else {
                        Some(node)
                    }
                }
                _ => Some(node),
            },
            |_idx, edge| Some(edge),
        );
        format!("{:?}", Dot::new(&new_graph))
    }

    fn dot_str_no_tmps_for_ctx(&self, fork_name: String) -> String where Self: AnalyzerLike, Self: Sized {
        let new_graph = self.graph().filter_map(
            |idx, node| match node {
                Node::Context(ctx) => {
                    if ctx.path != fork_name {
                        None
                    } else {
                        Some(node)
                    }
                }
                Node::ContextVar(_) => {
                    if let Some(ctx) = ContextVarNode::from(idx).maybe_ctx(self) {
                        if ctx.underlying(self).path == fork_name {
                            Some(node)
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                _ => Some(node),
            },
            |_idx, edge| Some(edge),
        );
        format!("{:?}", Dot::new(&new_graph))
    }
}


impl<T> Search for T where T: AnalyzerLike {}
pub trait Search: AnalyzerLike {
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