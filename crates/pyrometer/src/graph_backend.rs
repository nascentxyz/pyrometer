use crate::Analyzer;
use graph::elem::Elem;
use graph::nodes::Concrete;
use shared::RangeArena;

use graph::{
    as_dot_str, nodes::ContextNode, AnalyzerBackend, AsDotStr, ContextEdge, Edge, GraphBackend,
    Node,
};
use shared::{GraphDot, GraphLike, NodeIdx, Search};

use petgraph::{dot::Dot, graph::EdgeIndex, visit::EdgeRef, Directed, Direction, Graph};

use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

impl GraphLike for Analyzer {
    type Node = Node;
    type Edge = Edge;
    type RangeElem = Elem<Concrete>;
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        &mut self.graph
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        &self.graph
    }

    fn range_arena(&self) -> &RangeArena<Elem<Concrete>> {
        &self.range_arena
    }

    fn range_arena_mut(&mut self) -> &mut RangeArena<Elem<Concrete>> {
        &mut self.range_arena
    }
}

impl GraphBackend for Analyzer {}

impl GraphDot for Analyzer {
    fn cluster_str(
        &self,
        node: NodeIdx,
        cluster_num: &mut usize,
        is_killed: bool,
        handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
        handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
        depth: usize,
        as_mermaid: bool,
    ) -> Option<String>
    where
        Self: std::marker::Sized,
    {
        *cluster_num += 1;
        let curr_cluster = *cluster_num;

        // only used for mermaid
        let curr_cluster_name = format!(
            "cluster_{cluster_num}_{}",
            if is_killed && curr_cluster % 2 == 0 {
                "bgcolor_7a0b0b"
            } else if is_killed {
                "bgcolor_e04646"
            } else if curr_cluster % 2 == 0 {
                "bgcolor_252C46"
            } else {
                "bgcolor_1a1b26"
            }
        );

        if self
            .graph()
            .edges_directed(node, Direction::Outgoing)
            .collect::<Vec<_>>()
            .is_empty()
        {
            return None;
        }
        let new_graph = self.graph().filter_map(
            |_idx, node| match node {
                Node::ContextVar(_cvar) => Some(node.clone()),
                _ => Some(node.clone()),
            },
            |_idx, edge| Some(*edge),
        );

        let g = &G { graph: &new_graph };
        let children = g.children_exclude(node, 0, &[Edge::Context(ContextEdge::Subcontext)]);
        let mut children_edges = g
            .edges_for_nodes(&children)
            .into_iter()
            .filter(|(_, _, e, _)| *e != Edge::Context(ContextEdge::InputVariable))
            .collect::<BTreeSet<_>>();
        children_edges.extend(
            self.graph()
                .edges_directed(node, Direction::Incoming)
                .filter(|edge| *edge.weight() != Edge::Context(ContextEdge::InputVariable))
                .map(|edge| (edge.source(), edge.target(), *edge.weight(), edge.id()))
                .collect::<BTreeSet<(NodeIdx, NodeIdx, Edge, EdgeIndex<usize>)>>(),
        );
        let preindent = " ".repeat(4 * depth.saturating_sub(1));
        let indent = " ".repeat(4 * depth);
        let child_node_str = children
            .iter()
            .filter_map(|child| {
                let post_str = match self.node(*child) {
                    Node::Context(c) => {
                        *cluster_num += 2;
                        if let Some(inner) = self.cluster_str(
                            *child,
                            cluster_num,
                            c.killed.is_some(),
                            handled_nodes.clone(),
                            handled_edges.clone(),
                            depth + 1,
                            as_mermaid,
                        ) {
                            inner
                        } else {
                            "".to_string()
                        }
                    }
                    Node::ContextFork => {
                        let children = g.children_exclude(*child, 0, &[]);
                        let mut child_iter = children.iter();
                        let l_fork = child_iter.next()?;
                        let r_fork = child_iter.next()?;
                        let l_ctx = ContextNode::from(*l_fork);
                        let r_ctx = ContextNode::from(*r_fork);
                        *cluster_num += 1;
                        let l_fork = if let Some(inner) = self.cluster_str(
                            *l_fork,
                            cluster_num,
                            l_ctx.is_killed(self).ok()?,
                            handled_nodes.clone(),
                            handled_edges.clone(),
                            depth + 1,
                            as_mermaid,
                        ) {
                            inner
                        } else {
                            "".to_string()
                        };

                        *cluster_num += 2;
                        let r_fork = if let Some(inner) = self.cluster_str(
                            *r_fork,
                            cluster_num,
                            r_ctx.is_killed(self).ok()?,
                            handled_nodes.clone(),
                            handled_edges.clone(),
                            depth + 1,
                            as_mermaid,
                        ) {
                            inner
                        } else {
                            "".to_string()
                        };

                        format!("{l_fork}\n{r_fork}\n")
                    }
                    Node::FunctionCall => {
                        let children = g.children_exclude(*child, 0, &[]);
                        let mut child_iter = children.iter();
                        let func = child_iter.next()?;
                        let func_ctx = ContextNode::from(*func);
                        if let Some(inner) = self.cluster_str(
                            *func,
                            cluster_num,
                            func_ctx.is_killed(self).ok()?,
                            handled_nodes.clone(),
                            handled_edges.clone(),
                            depth + 1,
                            as_mermaid,
                        ) {
                            inner
                        } else {
                            "".to_string()
                        }
                    }
                    Node::ContextVar(_) => {
                        let mut children = g.children_exclude(
                            *child,
                            usize::MAX,
                            &[Edge::Context(ContextEdge::InputVariable)],
                        );
                        children.insert(*child);
                        children
                            .iter()
                            .map(|child| {
                                // if !handled_nodes.lock().unwrap().contains(child) {
                                //     return None
                                // } else {
                                //     handled_nodes.lock().unwrap().insert(*child);
                                // }
                                mermaid_node(self, &indent, *child, true, Some(&curr_cluster_name))
                            })
                            .collect::<Vec<_>>()
                            .join("\n")
                    }
                    _ => "".to_string(),
                };

                if as_mermaid {
                    if !post_str.is_empty() {
                        Some(post_str)
                    } else {
                        if !handled_nodes.lock().unwrap().contains(child) {
                            return None;
                        } else {
                            handled_nodes.lock().unwrap().insert(*child);
                        }
                        Some(mermaid_node(
                            self,
                            &indent,
                            *child,
                            true,
                            Some(&curr_cluster_name),
                        ))
                    }
                } else {
                    {
                        if !handled_nodes.lock().unwrap().contains(child) {
                            return None;
                        } else {
                            handled_nodes.lock().unwrap().insert(*child);
                        }
                    }
                    Some(format!(
                        "{indent}{} [label = \"{}\", color = \"{}\"]\n{}",
                        petgraph::graph::GraphIndex::index(child),
                        as_dot_str(*child, g).replace('\"', "\'"),
                        self.node(*child).dot_str_color(),
                        post_str
                    ))
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        let edge_str = children_edges
            .iter()
            .filter(|(_, _, _, idx)| !handled_edges.lock().unwrap().contains(idx))
            .map(|(from, to, edge, idx)| {
                handled_edges.lock().unwrap().insert(*idx);
                let from = petgraph::graph::GraphIndex::index(from);
                let to = petgraph::graph::GraphIndex::index(to);
                let edge_idx = idx.index();
                let edge_str = format!("{edge:?}").replace('"', "\'");
                if as_mermaid {
                    format!("{indent}{from:} -->|\"{edge_str}\"| {to:}\n{indent}class {to} linkSource{edge_idx}\n{indent}class {from} linkTarget{edge_idx}")
                } else {
                    format!("{indent}{from:} -> {to:} [label = \"{edge_str}\"]",)    
                }
            })
            .collect::<Vec<_>>()
            .join("\n");

        if as_mermaid {
            let node_str = {
                if handled_nodes.lock().unwrap().contains(&node) {
                    "".to_string()
                } else {
                    {
                        handled_nodes.lock().unwrap().insert(node);
                    }
                    mermaid_node(self, &indent, node, true, Some(&curr_cluster_name))
                }
            };

            let child_node_str = if child_node_str.is_empty() {
                "".into()
            } else {
                format!("\n{child_node_str}")
            };
            let edge_str = if edge_str.is_empty() {
                "".into()
            } else {
                format!("\n{edge_str}")
            };
            if node_str.is_empty() && child_node_str.is_empty() && edge_str.is_empty() {
                return None;
            }
            Some(format!(
                "{preindent}subgraph {curr_cluster_name}\n{node_str}{child_node_str}{edge_str}\n{preindent}end",
            ))
        } else {
            Some(format!(
                "{preindent}subgraph cluster_{} {{\n{}\n{}\n{}\n{}\n}}",
                cluster_num,
                if is_killed && curr_cluster % 2 == 0 {
                    format!("{indent}bgcolor=\"#7a0b0b\"")
                } else if is_killed {
                    format!("{indent}bgcolor=\"#e04646\"")
                } else if curr_cluster % 2 == 0 {
                    format!("{indent}bgcolor=\"#545e87\"")
                } else {
                    format!("{indent}bgcolor=\"#1a1b26\"")
                },
                format!(
                    "{indent}{} [label = \"{}\", color = \"{}\"]",
                    node.index(),
                    as_dot_str(node, g).replace('\"', "\'"),
                    self.node(node).dot_str_color()
                ),
                child_node_str,
                edge_str,
            ))
        }
    }

    fn dot_str(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerBackend,
    {
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26"; rankdir="BT"; splines=ortho;"##;
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
                if !handled_nodes.lock().unwrap().contains(node) {
                    match self.node(*node) {
                        Node::Function(_) => {
                            cluster_num += 2;
                            Some(self.cluster_str(
                                *node,
                                &mut cluster_num,
                                false,
                                handled_nodes.clone(),
                                handled_edges.clone(),
                                2,
                                false,
                            )?)
                        }
                        n => Some(format!(
                            "    {} [label = \"{}\", color = \"{}\"]",
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
            .join("\n");
        let edges_str = edges
            .into_iter()
            .filter_map(|edge| {
                if !handled_edges.lock().unwrap().contains(&edge) {
                    let (from, to) = self.graph().edge_endpoints(edge).unwrap();
                    if skip.contains(&from) || skip.contains(&to) {
                        return None;
                    }
                    let from = from.index();
                    let to = to.index();
                    Some(format!(
                        "    {from:} -> {to:} [label = \"{}\"]",
                        format!("{:?}", self.graph().edge_weight(edge).unwrap()).replace('"', "\'")
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        dot_str.push(nodes_str);
        dot_str.push(edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        dot_str.join("\n")
    }

    fn dot_str_no_tmps(&self) -> String
    where
        Self: std::marker::Sized,
        Self: GraphLike + AnalyzerBackend,
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
                        Edge::Context(edge) => {
                            format!("label = \"{}\"", format!("{edge:?}").replace('"', "\'"))
                        }
                        e => format!("label = \"{}\"", format!("{e:?}").replace('"', "\'")),
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

    fn mermaid_str(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerBackend,
    {
        let mut dot_str = Vec::new();
        let raw_start_str = r#"
%%{
  init : {
    'theme': 'base',
    'themeVariables': {
      'primaryColor': '#1a1b26',
      'primaryTextColor': '#d5daf0',
      'primaryBorderColor': '#7C0000',
      'lineColor': '#414868',
      'secondaryColor': '#24283b',
      'tertiaryColor': '#24283b'
    },
    "flowchart" : {
      "defaultRenderer": "elk"
    }
  }
}%%

flowchart BT
"#;
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
                if !handled_nodes.lock().unwrap().contains(node) {
                    match self.node(*node) {
                        Node::Function(_) => {
                            cluster_num += 2;
                            Some(self.cluster_str(
                                *node,
                                &mut cluster_num,
                                false,
                                handled_nodes.clone(),
                                handled_edges.clone(),
                                2,
                                true,
                            )?)
                        }
                        Node::ContextVar(_) => None,
                        n => {
                            handled_nodes.lock().unwrap().insert(*node);
                            Some(format!(
                                "    {}(\"{}\")\n    style {} stroke:{}",
                                petgraph::graph::GraphIndex::index(node),
                                as_dot_str(*node, self).replace('\"', "\'"),
                                petgraph::graph::GraphIndex::index(node),
                                n.dot_str_color()
                            ))
                        }
                    }
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let edges_str = edges
            .into_iter()
            .filter_map(|edge| {
                if !handled_edges.lock().unwrap().contains(&edge) {
                    let (from, to) = self.graph().edge_endpoints(edge).unwrap();
                    if skip.contains(&from) || skip.contains(&to) {
                        return None;
                    }
                    let from = from.index();
                    let to = to.index();
                    let edge_idx = edge.index();
                    Some(format!(
                        "    {from:} -->|\"{}\"| {to:}\n    class {to} linkSource{edge_idx}\n    class {from} linkTarget{edge_idx}",
                        format!("{:?}", self.graph().edge_weight(edge).unwrap()).replace('"', "\'")
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        dot_str.push(nodes_str);
        dot_str.push(edges_str);
        dot_str.join("\n")
    }
}

struct G<'a> {
    pub graph: &'a Graph<Node, Edge, Directed, usize>,
}

impl GraphLike for G<'_> {
    type Node = Node;
    type Edge = Edge;
    type RangeElem = Elem<Concrete>;
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        panic!("Should not call this")
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        self.graph
    }
    fn range_arena(&self) -> &RangeArena<Elem<Concrete>> {
        panic!("Should not call this")
    }
    fn range_arena_mut(&mut self) -> &mut RangeArena<Elem<Concrete>> {
        panic!("Should not call this")
    }
}

impl GraphBackend for G<'_> {}

pub fn mermaid_node(
    g: &impl GraphBackend,
    indent: &str,
    node: NodeIdx,
    style: bool,
    class: Option<&str>,
) -> String {
    let mut node_str = format!(
        "{indent}{}(\"{}\")",
        petgraph::graph::GraphIndex::index(&node),
        as_dot_str(node, g).replace('\"', "\'"),
    );

    if style {
        node_str.push_str(&format!(
            "\n{indent}style {} stroke:{}",
            petgraph::graph::GraphIndex::index(&node),
            g.node(node).dot_str_color()
        ));
    }

    if let Some(class) = class {
        node_str.push_str(&format!(
            "\n{indent}class {} {class}",
            petgraph::graph::GraphIndex::index(&node),
        ));
    }

    node_str
}
