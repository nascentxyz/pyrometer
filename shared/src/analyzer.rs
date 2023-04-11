use crate::as_dot_str;
use crate::range::Range;
use crate::BlockNode;

use crate::MsgNode;
use std::sync::Arc;
use std::sync::Mutex;

use crate::context::ContextVarNode;
use crate::range::range_string::ToRangeString;
use crate::{Builtin, Edge, Function, FunctionParam, FunctionReturn, Node, NodeIdx};
use petgraph::visit::EdgeRef;
use std::collections::BTreeMap;
use std::collections::BTreeSet;

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
    fn user_types(&self) -> &HashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    fn parse_expr(&mut self, expr: &Self::Expr) -> NodeIdx;
    fn msg(&mut self) -> MsgNode;
    fn block(&mut self) -> BlockNode;
    fn entry(&self) -> NodeIdx;
}

struct G<'a> {
    pub graph: &'a Graph<Node, Edge, Directed, usize>,
}
impl GraphLike for G<'_> {
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        panic!("Should call this")
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        self.graph
    }
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

    fn open_dot(&self)
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        use std::env::temp_dir;
        use std::fs;
        use std::io::Write;
        use std::process::Command;
        let mut dir = temp_dir();
        let file_name = "dot.dot";
        dir.push(file_name);

        let mut file = fs::File::create(dir.clone()).unwrap();
        file.write_all(self.dot_str().as_bytes()).unwrap();
        Command::new("dot")
            .arg("-Tsvg")
            .arg(dir)
            .arg("-o")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
        Command::new("open")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
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

    fn cluster_str(
        &self,
        node: NodeIdx,
        cluster_num: usize,
        handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
        handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
    ) -> String {
        let new_graph = self.graph().filter_map(
            |_idx, node| match node {
                Node::ContextVar(_cvar) => {
                    // if !cvar.is_symbolic {
                    //     None
                    // } else {
                    Some(node.clone())
                    // }
                }
                _ => Some(node.clone()),
            },
            |_idx, edge| Some(*edge),
        );

        let g = &G { graph: &new_graph };
        let children = g.children(node);
        let children_edges = g.children_edges(node);
        let mut cn = cluster_num + 1;
        let child_node_str = children
            .iter()
            .map(|child| {
                {
                    handled_nodes.lock().unwrap().insert(*child);
                }
                let post_str = match self.node(*child) {
                    Node::Context(_) => {
                        cn += 2;
                        self.cluster_str(*child, cn, handled_nodes.clone(), handled_edges.clone())
                    }
                    _ => "".to_string(),
                };

                format!(
                    "        {} [label = \"{}\", color = \"{}\"]\n{}\n",
                    petgraph::graph::GraphIndex::index(child),
                    as_dot_str(*child, g).replace('\"', "\'"),
                    self.node(*child).dot_str_color(),
                    post_str
                )
            })
            .collect::<Vec<_>>()
            .join("");

        let edge_str = children_edges
            .iter()
            .filter(|(_, _, _, idx)| !handled_edges.lock().unwrap().contains(idx))
            .map(|(from, to, edge, idx)| {
                handled_edges.lock().unwrap().insert(*idx);
                let from = petgraph::graph::GraphIndex::index(from);
                let to = petgraph::graph::GraphIndex::index(to);
                format!("        {from:} -> {to:} [label = \"{edge:?}\"]\n",)
            })
            .collect::<Vec<_>>()
            .join("");
        format!(
            "    subgraph cluster_{} {{\n{}\n{}\n{}\n{}\n}}",
            cluster_num,
            if cluster_num % 2 == 0 {
                "        bgcolor=\"#545e87\""
            } else {
                "        bgcolor=\"#1a1b26\""
            },
            format!(
                "        {} [label = \"{}\", color = \"{}\"]\n",
                node.index(),
                as_dot_str(node, g).replace('\"', "\'"),
                self.node(node).dot_str_color()
            ),
            child_node_str,
            edge_str,
        )
    }

    // fn ctx_cluster_str(
    //     &self,
    //     ctx_node: ContextNode,
    //     cluster_num: usize,
    //     handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
    //     handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
    // ) -> String {
    //     let new_graph = self.graph().filter_map(
    //         |_idx, node| match node {
    //             Node::ContextVar(_cvar) => {
    //                 // if !cvar.is_symbolic {
    //                 //     None
    //                 // } else {
    //                 Some(node.clone())
    //                 // }
    //             }
    //             _ => Some(node.clone()),
    //         },
    //         |_idx, edge| Some(*edge),
    //     );

    //     let g = &G { graph: &new_graph };
    //     let children = g.children(ctx_node.0.into());
    //     let children_edges = g.children_edges(ctx_node.0.into());
    //     format!(
    //         "    subgraph cluster_{} {{\n{}\n{}\n{}\n{}\n}}",
    //         cluster_num,
    //         if cluster_num % 2 == 0 { "        bgcolor=\"#545e87\"" } else {  "        bgcolor=\"#1a1b26\"" },
    //         format!(
    //             "        {} [label = \"{}\", color = \"{}\"]\n",
    //             func_node.0,
    //             as_dot_str(func_node.0.into(), g).replace('\"', "\'"),
    //             self.node(NodeIdx::from(func_node.0)).dot_str_color()
    //         ),
    //         children
    //             .iter()
    //             .map(|child| {
    //                 handled_nodes.lock().unwrap().insert(*child);
    //                 format!(
    //                     "        {} [label = \"{}\", color = \"{}\"]\n",
    //                     petgraph::graph::GraphIndex::index(child),
    //                     as_dot_str(*child, g).replace('\"', "\'"),
    //                     self.node(*child).dot_str_color()
    //                 )
    //             })
    //             .collect::<Vec<_>>()
    //             .join(""),
    //         children_edges
    //             .iter()
    //             .filter(|(_, _, _, idx)| { !handled_edges.lock().unwrap().contains(idx) })
    //             .map(|(from, to, edge, idx)| {
    //                 handled_edges.lock().unwrap().insert(*idx);
    //                 let from = petgraph::graph::GraphIndex::index(from);
    //                 let to = petgraph::graph::GraphIndex::index(to);
    //                 format!("        {from:} -> {to:} [label = \"{edge:?}\"]\n",)
    //             })
    //             .collect::<Vec<_>>()
    //             .join(""),
    //     )
    // }

    fn dot_str(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26"; rankdir="BT""##;
        dot_str.push(raw_start_str.to_string());
        let handled_edges = Arc::new(Mutex::new(BTreeSet::new()));
        let handled_nodes = Arc::new(Mutex::new(BTreeSet::new()));
        let (nodes, edges) = (
            self.graph().node_indices().collect::<Vec<_>>(),
            self.graph().edge_indices().collect::<Vec<_>>(),
        );
        let mut cluster_num = 0;
        let nodes_str = nodes
            .iter()
            .filter_map(|node| {
                if !handled_nodes.lock().unwrap().contains(node) {
                    match self.node(*node) {
                        Node::Function(_) => {
                            cluster_num += 2;
                            Some(self.cluster_str(
                                *node,
                                cluster_num,
                                handled_nodes.clone(),
                                handled_edges.clone(),
                            ))
                        }
                        n => Some(format!(
                            "{} [label = \"{}\", color = \"{}\"]",
                            petgraph::graph::GraphIndex::index(node),
                            as_dot_str(*node, self).replace('\"', "\'"),
                            n.dot_str_color()
                        )),
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n    ");
        let edges_str = edges
            .into_iter()
            .filter_map(|edge| {
                if !handled_edges.lock().unwrap().contains(&edge) {
                    let (from, to) = self.graph().edge_endpoints(edge).unwrap();
                    let from = from.index();
                    let to = to.index();
                    Some(format!(
                        "{from:} -> {to:} [label = \"{:?}\"]",
                        self.graph().edge_weight(edge).unwrap()
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n    ");

        dot_str.push(nodes_str);
        dot_str.push(edges_str);
        // let nodes_and_edges_str = format!(
        //     "{:?}",
        //     Dot::with_attr_getters(
        //         &new_graph,
        //         &[
        //             petgraph::dot::Config::GraphContentOnly,
        //             petgraph::dot::Config::NodeNoLabel,
        //             petgraph::dot::Config::EdgeNoLabel
        //         ],
        //         &|_graph, edge_ref| {
        //             match edge_ref.weight() {
        //                 Edge::Context(edge) => format!("label = \"{edge:?}\""),
        //                 e => format!("label = \"{e:?}\""),
        //             }
        //         },
        //         &|_graph, (idx, node_ref)| {
        //             let dot_str = match node_ref {
        //                 Node::ContextVar(cvar) => {
        //                     // we have to do this special because dynamic elements in ranges aren't guaranteed
        //                     // to stick around
        //                     let range_str = if let Some(r) = cvar.ty.range(self) {
        //                         r.as_dot_str(self)
        //                         // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
        //                     } else {
        //                         "".to_string()
        //                     };

        //                     format!(
        //                         "{} -- {} -- range: {}, loc: {:?}",
        //                         cvar.display_name,
        //                         cvar.ty.as_string(self),
        //                         range_str,
        //                         cvar.loc
        //                     )
        //                 }
        //                 _ => as_dot_str(idx, &G { graph: &new_graph }),
        //             };
        //             format!(
        //                 "label = \"{}\", color = \"{}\"",
        //                 dot_str.replace('\"', "\'"),
        //                 node_ref.dot_str_color()
        //             )
        //         }
        //     )
        // );
        // dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        dot_str.join("\n")
    }

    fn dot_str_no_tmps(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        let new_graph = self.graph().filter_map(
            |_idx, node| match node {
                Node::ContextVar(cvar) => {
                    if !cvar.is_symbolic || cvar.tmp_of.is_some() {
                        None
                    } else {
                        Some(node.clone())
                    }
                }
                _ => Some(node.clone()),
            },
            |_idx, edge| Some(*edge),
        );
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());
        let nodes_and_edges_str = format!(
            "{:?}",
            Dot::with_attr_getters(
                &new_graph,
                &[
                    petgraph::dot::Config::GraphContentOnly,
                    petgraph::dot::Config::NodeNoLabel,
                    petgraph::dot::Config::EdgeNoLabel
                ],
                &|_graph, edge_ref| {
                    match edge_ref.weight() {
                        Edge::Context(edge) => format!("label = \"{edge:?}\""),
                        e => format!("label = \"{e:?}\""),
                    }
                },
                &|_graph, (idx, node_ref)| {
                    let inner = match node_ref {
                        Node::ContextVar(cvar) => {
                            let range_str = if let Some(r) = cvar.ty.range(self) {
                                r.as_dot_str(self)
                                // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(self),
                                range_str
                            )
                        }
                        _ => as_dot_str(idx, &G { graph: &new_graph }),
                    };
                    format!(
                        "label = \"{}\", color = \"{}\"",
                        inner.replace('\"', "\'"),
                        node_ref.dot_str_color()
                    )
                }
            )
        );
        dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        dot_str.join("\n")
    }

    fn dot_str_no_tmps_for_ctx(&self, fork_name: String) -> String
    where
        Self: AnalyzerLike,
        Self: Sized,
    {
        let new_graph = self.graph().filter_map(
            |idx, node| match node {
                Node::Context(ctx) => {
                    if ctx.path != fork_name {
                        None
                    } else {
                        Some(node.clone())
                    }
                }
                Node::ContextVar(cvar) => {
                    if let Some(ctx) = ContextVarNode::from(idx).maybe_ctx(self) {
                        if ctx.underlying(self).path == fork_name && !cvar.is_symbolic {
                            Some(node.clone())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                _ => Some(node.clone()),
            },
            |_idx, edge| Some(*edge),
        );
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());
        let nodes_and_edges_str = format!(
            "{:?}",
            Dot::with_attr_getters(
                &new_graph,
                &[
                    petgraph::dot::Config::GraphContentOnly,
                    petgraph::dot::Config::NodeNoLabel,
                    petgraph::dot::Config::EdgeNoLabel
                ],
                &|_graph, edge_ref| {
                    match edge_ref.weight() {
                        Edge::Context(edge) => format!("label = \"{edge:?}\""),
                        e => format!("label = \"{e:?}\""),
                    }
                },
                &|_graph, (idx, node_ref)| {
                    let inner = match node_ref {
                        Node::ContextVar(cvar) => {
                            let range_str = if let Some(r) = cvar.ty.range(self) {
                                format!(
                                    "[{}, {}]",
                                    r.evaled_range_min(self).to_range_string(false, self).s,
                                    r.evaled_range_max(self).to_range_string(true, self).s
                                )
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(self),
                                range_str
                            )
                        }
                        _ => as_dot_str(idx, &G { graph: &new_graph }),
                    };
                    format!(
                        "label = \"{}\", color = \"{}\"",
                        inner.replace('\"', "\'"),
                        node_ref.dot_str_color()
                    )
                }
            )
        );
        dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        dot_str.join("\n")
    }
}

impl<T> Search for T where T: GraphLike {}
pub trait Search: GraphLike {
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

    fn search_children_depth(&self, start: NodeIdx, edge_ty: &Edge, max_depth: usize, curr_depth: usize) -> BTreeSet<NodeIdx> {
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
                    .flat_map(|edge| self.search_children_depth(edge.source(), edge_ty, max_depth, curr_depth + 1))
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

pub trait AsDotStr {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String;
}
