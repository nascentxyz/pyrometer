use crate::as_dot_str;

use crate::FunctionParamNode;

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

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub enum GraphError {
    NodeConfusion(String),
    MaxStackDepthReached(String),
    MaxStackWidthReached(String),
    ChildRedefinition(String),
    VariableUpdateInOldContext(String),
    DetachedVariable(String),
    ExpectedSingle(String),
    StackLengthMismatch(String),
    UnbreakableRecursion(String),
}

pub trait AnalyzerLike: GraphLike {
    type Expr;
    type ExprErr;
    /// Gets the builtin functions map
    fn builtin_fns(&self) -> &HashMap<String, Function>;
    /// Mutably gets the builtin functions map
    fn builtin_fn_nodes_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    /// Gets the builtin function nodes mapping
    fn builtin_fn_nodes(&self) -> &HashMap<String, NodeIdx>;
    /// Returns the configured max call depth
    fn max_depth(&self) -> usize;
    /// Returns the configured max fork width
    fn max_width(&self) -> usize;
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
    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized,
    {
        if let Some(idx) = self.builtin_fn_nodes().get(builtin_name) {
            Some(*idx)
        } else if let Some(func) = self.builtin_fns().get(builtin_name) {
            let (inputs, outputs) = self
                .builtin_fn_inputs()
                .get(builtin_name)
                .expect("builtin func but no inputs")
                .clone();
            let func_node = self.add_node(Node::Function(func.clone()));
            let mut params_strs = vec![];
            inputs.into_iter().for_each(|input| {
                let input_node = self.add_node(input);
                params_strs.push(FunctionParamNode::from(input_node).ty_str(self).unwrap());
                self.add_edge(input_node, func_node, Edge::FunctionParam);
            });
            outputs.into_iter().for_each(|output| {
                let output_node = self.add_node(output);
                self.add_edge(output_node, func_node, Edge::FunctionReturn);
            });

            self.add_edge(func_node, self.entry(), Edge::Func);

            self.builtin_fn_nodes_mut()
                .insert(builtin_name.to_string(), func_node);
            Some(func_node)
        } else {
            None
        }
    }
    fn user_types(&self) -> &HashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    fn parse_expr(&mut self, expr: &Self::Expr, parent: Option<NodeIdx>) -> NodeIdx;
    fn msg(&mut self) -> MsgNode;
    fn block(&mut self) -> BlockNode;
    fn entry(&self) -> NodeIdx;

    fn add_expr_err(&mut self, err: Self::ExprErr);

    fn add_if_err<T>(&mut self, err: Result<T, Self::ExprErr>) -> Option<T> {
        match err {
            Ok(t) => Some(t),
            Err(e) => {
                self.add_expr_err(e);
                None
            }
        }
    }

    fn expr_errs(&self) -> Vec<Self::ExprErr>;
}

pub struct G<'a> {
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
        let temp_dir = temp_dir();
        let file_name = "dot.dot";
        let mut temp_path = temp_dir.clone();
        temp_path.push(file_name);
        let temp_svg_filename: String = format!("{}/dot.svg", &temp_dir.to_string_lossy());

        let mut file = fs::File::create(temp_path.clone()).unwrap();
        file.write_all(self.dot_str().as_bytes()).unwrap();
        Command::new("dot")
            .arg("-Tsvg")
            .arg(temp_path)
            .arg("-o")
            .arg(&temp_svg_filename)
            .output()
            .expect("You may need to install graphviz, check if command 'dot' is in your $PATH");
        Command::new("open")
            .arg(&temp_svg_filename)
            .spawn()
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
        if petgraph::algo::is_cyclic_directed(self.graph()) {
            panic!("Cyclic graph");
        }
    }

    fn cluster_str(
        &self,
        node: NodeIdx,
        cluster_num: usize,
        is_killed: bool,
        handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
        handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
    ) -> String {
        if self
            .graph()
            .edges_directed(node, Direction::Outgoing)
            .collect::<Vec<_>>()
            .is_empty()
        {
            return "".to_string();
        }
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

                if g.graph
                    .edges_directed(*child, Direction::Outgoing)
                    .collect::<Vec<_>>()
                    .is_empty()
                {
                    return "".to_string();
                }
                let post_str = match self.node(*child) {
                    Node::Context(c) => {
                        cn += 2;
                        self.cluster_str(
                            *child,
                            cn,
                            c.killed.is_some(),
                            handled_nodes.clone(),
                            handled_edges.clone(),
                        )
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
            if is_killed && cluster_num % 2 == 0 {
                "        bgcolor=\"#7a0b0b\""
            } else if is_killed {
                "        bgcolor=\"#e04646\""
            } else if cluster_num % 2 == 0 {
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
        let mut skip = BTreeSet::default();
        let nodes_str = nodes
            .iter()
            .filter_map(|node| {
                if self
                    .graph()
                    .edges_directed(*node, Direction::Outgoing)
                    .collect::<Vec<_>>()
                    .is_empty()
                    && !matches!(self.node(*node), Node::Entry)
                {
                    skip.insert(*node);
                    return None;
                }
                let handled_nodes_contains = {
                    handled_nodes.lock().unwrap().contains(node)
                };
                if !handled_nodes_contains {
                    match self.node(*node) {
                        Node::Function(_) => {
                            cluster_num += 2;
                            Some(self.cluster_str(
                                *node,
                                cluster_num,
                                false,
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
                let handled_edges_contains = {
                    handled_edges.lock().unwrap().contains(&edge)
                };
                if !handled_edges_contains {
                    let (from, to) = self.graph().edge_endpoints(edge).unwrap();
                    if skip.contains(&from) || skip.contains(&to) {
                        return None;
                    }
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
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        dot_str.join("\n")
    }

    fn dot_str_no_tmps(&self) -> String
    where
        Self: std::marker::Sized,
        Self: GraphLike + AnalyzerLike,
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
                            let range_str = if let Some(r) = cvar.ty.ref_range(self).unwrap() {
                                r.as_dot_str(self)
                                // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(self).unwrap(),
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
        Self: GraphLike + AnalyzerLike,
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
                        if ctx.underlying(self).unwrap().path == fork_name && !cvar.is_symbolic {
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
                            let range_str = if let Some(r) = cvar.ty.ref_range(self).unwrap() {
                                format!(
                                    "[{}, {}]",
                                    r.evaled_range_min(self)
                                        .unwrap()
                                        .to_range_string(false, self)
                                        .s,
                                    r.evaled_range_max(self)
                                        .unwrap()
                                        .to_range_string(true, self)
                                        .s
                                )
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(self).unwrap(),
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

pub trait AsDotStr {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String;
}
