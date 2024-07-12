use crate::Analyzer;
use graph::{
    as_dot_str,
    elem::{Elem, RangeElem},
    nodes::{Concrete, ContextNode, ContextVarNode},
    AnalyzerBackend, AsDotStr, ContextEdge, Edge, GraphBackend, Node, TOKYO_NIGHT_COLORS,
};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use shared::RangeArena;
use shared::{GraphDot, GraphLike, NodeIdx, Search};
use std::collections::hash_map::DefaultHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::{collections::HashMap, fmt::Display};
use tokio::runtime::Runtime;
use tracing::{error, trace, warn};

use petgraph::{dot::Dot, graph::EdgeIndex, visit::EdgeRef, Directed, Direction, Graph};
use std::convert::TryFrom;
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

    fn mark_dirty(&mut self, node: NodeIdx) {
        self.dirty_nodes.insert(node);
    }

    fn dirty_nodes(&self) -> &BTreeSet<NodeIdx> {
        &self.dirty_nodes
    }
    fn dirty_nodes_mut(&mut self) -> &mut BTreeSet<NodeIdx> {
        &mut self.dirty_nodes
    }
}

pub fn post_to_site_arena(arena_str: String) {
    let rt = Runtime::new().unwrap();
    rt.block_on(async {
        post_to_site_arena_async(arena_str).await;
    });
}

async fn post_to_site_arena_async(arena_str: String) {
    let client = Client::new();
    let graph_msg = ArenaMessage {
        arena: arena_str.to_string(),
    };

    let res = client
        .post("http://127.0.0.1:8545/updatearena")
        .json(&graph_msg)
        .send()
        .await
        .expect("Failed to send request");

    if res.status().is_success() {
        trace!("Successfully posted arena to site");
    } else {
        error!("Failed to post arena to site: {:?}", res.status());
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
struct ArenaMessage {
    arena: String,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
pub enum ArenaNode {
    /// Arena node (index)
    ARENA(usize),
    /// ContextVar node (label is the string representation of the node)
    CVAR(String),
    /// Elem node (e.g. an expression) (label is the string representation of the node)
    ELEM(String),
}

impl Display for ArenaNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // warning: changing these will impact the pyro-debug site when rendering edge styling
        let variant_name = match self {
            ArenaNode::ARENA(idx) => format!("index {}", idx),
            ArenaNode::ELEM(label) => label.to_string(),
            ArenaNode::CVAR(label) => label.to_string(),
        };
        write!(f, "{}", variant_name)
    }
}

impl ArenaNode {
    pub fn dot_str_color(&self) -> String {
        let c = match self {
            ArenaNode::ARENA(_) => TOKYO_NIGHT_COLORS.get("red1").unwrap(),
            ArenaNode::CVAR(_) => TOKYO_NIGHT_COLORS.get("deeporange").unwrap(),
            ArenaNode::ELEM(_) => TOKYO_NIGHT_COLORS.get("blue0").unwrap(),
        };
        c.to_string()
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash)]
pub enum ArenaEdge {
    LHS,
    RHS,
    ARENA,
    VAR,
    REF,
    MIN,
    MAX,
    NONE,
}

impl Display for ArenaEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // warning: changing these will impact the pyro-debug site when rendering edge styling
        let variant_name = match self {
            ArenaEdge::LHS => "LHS",
            ArenaEdge::RHS => "RHS",
            ArenaEdge::ARENA => "ARENA",
            ArenaEdge::VAR => "VAR",
            ArenaEdge::MIN => "MIN",
            ArenaEdge::MAX => "MAX",
            ArenaEdge::REF => "REF",
            ArenaEdge::NONE => "",
        };
        write!(f, "{}", variant_name)
    }
}

#[derive(Debug)]
pub enum ElemsError {
    BorrowError(String),
    MissingMap(String),
}

impl std::fmt::Display for ElemsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ElemsError::BorrowError(msg) => write!(f, "BorrowError: {}", msg),
            ElemsError::MissingMap(msg) => write!(f, "MissingMap: {}", msg),
        }
    }
}
impl std::error::Error for ElemsError {}
pub struct Elems {
    /// arena_idx, elem
    pub inner: Vec<(usize, Elem<Concrete>)>,
}

impl TryFrom<&RangeArena<Elem<Concrete>>> for Elems {
    type Error = ElemsError;
    fn try_from(arena: &RangeArena<Elem<Concrete>>) -> Result<Self, Self::Error> {
        // Collect the elements and their indices first from ranges
        // Collect the elements and their indices first from ranges
        let mut inner = Vec::new();
        for elem in &arena.ranges {
            // Get the map value
            if let Some(map_value) = arena.map.get(elem).copied() {
                // println!("Adding idx {} to elems {}", map_value, elem);
                inner.push((map_value, elem.clone()));
            } else {
                // println!("NONE REF elem: {:?}", elem);
                return Err(ElemsError::MissingMap(format!("elem {:?}", elem)));
            }
        }

        // Search .map for any entries that werent in .ranges
        let inner_indices: BTreeSet<_> = inner.iter().map(|(idx, _)| *idx).collect();
        let missing_entries: Vec<_> = arena
            .map
            .iter()
            .filter(|(_, &v)| !inner_indices.contains(&v))
            .collect();

        {
            // Log out missing entries
            let missing_entries_str = missing_entries
                .iter()
                .map(|(idx, elem)| format!("\telem {}: {}", idx, elem))
                .collect::<Vec<_>>()
                .join("\n");
            warn!(
                "`RangeArena.ranges` is missing {} entries from the map:\n{}",
                missing_entries.len(),
                missing_entries_str
            );
        }

        // Add any missing entries to inner
        for (_elem, &idx) in missing_entries {
            if let Some(range_elem) = arena.ranges.get(idx) {
                inner.push((idx, range_elem.clone()));
            }
        }

        // Sort the collected elements by their indices
        inner.sort_by(|a, b| a.0.cmp(&b.0));
        // dedup is needed as there are duplicate indices in the inner vec. TODO @brock is this a bug? arena has duplicate elems
        inner.dedup();

        // Print out elems
        // for (idx, elem) in inner.iter() {
        //     println!("elem {}: {}", idx, elem);
        // }

        Ok(Elems { inner })
    }
}

impl Elems {
    /// Convert Elems into a Graph
    ///
    /// First pass:
    /// - create nodes for each arena index
    ///   - this is needed separately, since when making edges some earlier nodes point to later nodes (that havent been made yet)
    ///
    /// Second pass:
    /// - create an edge between each arena index and the elem that it represents, make an edge between them
    /// - if elem is a reference, create nodes for the ContextVar that it depends on, make an edge from the elem to the ContextVar
    ///
    /// Third pass:
    /// - for each ContextVar node, create edges to the arena indices that it depends on
    ///
    pub fn to_graph(
        &self,
        graph_backend: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Graph<ArenaNode, ArenaEdge, Directed, usize> {
        let mut graph = Graph::default();
        let mut arena_idx_to_node_idx = HashMap::new();
        let mut dependency_map: HashMap<ContextVarNode, petgraph::graph::NodeIndex<usize>> =
            HashMap::new();

        // FIRST PASS: create nodes for each arena index
        self.inner.iter().for_each(|(arena_idx, _elem)| {
            // add an arena node to the graph for the index
            let arena_node_idx = graph.add_node(ArenaNode::ARENA(*arena_idx));
            arena_idx_to_node_idx.insert(arena_idx, arena_node_idx);
        });

        // SECOND PASS: create an edge between each arena index and the elem that it represents
        self.inner.iter().for_each(|(arena_idx, elem)| {
            // get the arena_node_idx for the arena index
            let arena_node_idx = arena_idx_to_node_idx.get(arena_idx).unwrap();

            // add a node for what the arena index has underlying it, and maybe edges for that elem
            let underlying_node_idx = match elem {
                Elem::Reference(_reference) => {
                    let node_str = elem.arena_graph_node_label();
                    let node_idx = graph.add_node(ArenaNode::ELEM(node_str));

                    // attempt to add in the ContextVar node that the elem is referencing
                    let context_var_nodes = elem
                        .dependent_on(graph_backend, arena)
                        .into_iter()
                        .collect::<Vec<_>>();
                    context_var_nodes.into_iter().for_each(|dep_elem| {
                        let dep_node_idx =
                            if let Some(&existing_node_idx) = dependency_map.get(&dep_elem) {
                                // don't make a new ContextVar node, just use the existing one
                                existing_node_idx
                            } else {
                                // make a new ContextVar Node for the Arena graph
                                let new_node_idx = graph.add_node(ArenaNode::CVAR(
                                    dep_elem.as_dot_str(graph_backend, arena).to_string(),
                                ));
                                dependency_map.insert(dep_elem, new_node_idx);
                                new_node_idx
                            };
                        // add an edge from the node to its dependency node
                        graph.add_edge(node_idx, dep_node_idx, ArenaEdge::VAR);
                    });

                    node_idx
                }
                Elem::ConcreteDyn(_range_dyn) => {
                    let node_str = elem.arena_graph_node_label();

                    graph.add_node(ArenaNode::ELEM(node_str))
                }
                Elem::Concrete(_range_concrete) => {
                    let node_str = elem.arena_graph_node_label();

                    graph.add_node(ArenaNode::ELEM(node_str))
                }
                Elem::Expr(range_expr) => {
                    let node_str = elem.arena_graph_node_label();
                    let node_idx = graph.add_node(ArenaNode::ELEM(node_str));

                    // Unbox and check the lhs and rhs to see if they are arena indices
                    let lhs_arena = match *range_expr.lhs.clone() {
                        Elem::Arena(lhs) => Some(lhs),
                        Elem::Reference(_lhs) => {
                            // println!("LHS is a reference: {}", range_expr.lhs);
                            // attempt to add in the ContextVar node that the elem is referencing
                            let context_var_nodes = elem
                                .dependent_on(graph_backend, arena)
                                .into_iter()
                                .collect::<Vec<_>>();
                            context_var_nodes.iter().for_each(|dep_elem| {
                                let dep_node_idx = if let Some(&existing_node_idx) =
                                    dependency_map.get(dep_elem)
                                {
                                    // don't make a new ContextVar node, just use the existing one
                                    existing_node_idx
                                } else {
                                    // make a new ContextVar Node for the Arena graph
                                    let new_node_idx = graph.add_node(ArenaNode::CVAR(
                                        dep_elem.as_dot_str(graph_backend, arena).to_string(),
                                    ));
                                    dependency_map.insert(*dep_elem, new_node_idx);
                                    new_node_idx
                                };
                                // use `update_edge` to avoid adding duplicate edges
                                graph.update_edge(node_idx, dep_node_idx, ArenaEdge::VAR);
                            });
                            None
                        }
                        _ => None,
                    };
                    let rhs_arena = match *range_expr.rhs.clone() {
                        Elem::Arena(rhs) => {
                            // println!("RHS is an arena index: {}", range_expr.rhs);
                            Some(rhs)
                        }
                        Elem::Reference(_rhs) => {
                            // println!("RHS is a reference: {}", range_expr.rhs);
                            // attempt to add in the ContextVar node that the elem is referencing
                            let context_var_nodes = elem
                                .dependent_on(graph_backend, arena)
                                .into_iter()
                                .collect::<Vec<_>>();
                            context_var_nodes.iter().for_each(|dep_elem| {
                                let dep_node_idx = if let Some(&existing_node_idx) =
                                    dependency_map.get(dep_elem)
                                {
                                    // don't make a new ContextVar node, just use the existing one
                                    existing_node_idx
                                } else {
                                    // make a new ContextVar Node for the Arena graph
                                    let new_node_idx = graph.add_node(ArenaNode::CVAR(
                                        dep_elem.as_dot_str(graph_backend, arena).to_string(),
                                    ));
                                    dependency_map.insert(*dep_elem, new_node_idx);
                                    new_node_idx
                                };
                                // use `update_edge` to avoid adding duplicate edges
                                graph.update_edge(node_idx, dep_node_idx, ArenaEdge::VAR);
                            });
                            None
                        }
                        _ => None,
                    };

                    // Add edges to the arena indices if they exist
                    if let Some(lhs_idx) = lhs_arena {
                        if let Some(&lhs_node_idx) = arena_idx_to_node_idx.get(&lhs_idx) {
                            graph.add_edge(node_idx, lhs_node_idx, ArenaEdge::LHS);
                        }
                    }

                    if let Some(rhs_idx) = rhs_arena {
                        if let Some(&rhs_node_idx) = arena_idx_to_node_idx.get(&rhs_idx) {
                            graph.add_edge(node_idx, rhs_node_idx, ArenaEdge::RHS);
                        }
                    }
                    node_idx
                }
                Elem::Arena(range_arena_idx) => {
                    panic!(
                        "Arena index in elems: {:?}. This should not happen!",
                        range_arena_idx
                    );
                }
                Elem::Null => {
                    let node_str = "null".to_string();

                    graph.add_node(ArenaNode::ELEM(node_str))
                }
            };

            // draw edge from the arena_node to the underlying node
            graph.add_edge(*arena_node_idx, underlying_node_idx, ArenaEdge::NONE);
        });

        // THIRD PASS - iterate over ContextVarNodes
        // iterate over the dependency map and add edges between the ContextVar nodes and the arena nodes
        // println!("dependency map: {:?}", dependency_map);
        for (cvar_node, &node_idx) in dependency_map.iter() {
            // println!("cvar node: {:?}, node idx: {:?}", cvar_node, node_idx);
            // Find the appropriate arena_idx for range.min and range.max using Elems.inner
            if let Ok(Some(range_min)) = cvar_node.range_min(graph_backend) {
                // println!(" range min: {:?}", range_min);
                match range_min {
                    Elem::Arena(arena_idx) => {
                        // Make a direct edge to the arena node
                        // println!("  arena idx: {}", arena_idx);
                        if let Some(&min_node_idx) = arena_idx_to_node_idx.get(&arena_idx) {
                            graph.add_edge(node_idx, min_node_idx, ArenaEdge::MIN);
                        }
                    }
                    _ => {
                        // attempt to find the elem in our `inner` and get the associated arena_graph index
                        let min_arena_idx = self
                            .inner
                            .iter()
                            .find(|(_, elem)| elem == &range_min)
                            .map(|(idx, _)| *idx);
                        // Add edges to the min arena indices
                        if let Some(min_idx) = min_arena_idx {
                            // println!("  min idx: {:?}", min_idx);
                            if let Some(&min_node_idx) = arena_idx_to_node_idx.get(&min_idx) {
                                // println!("   min node idx: {:?}", min_node_idx);
                                graph.add_edge(node_idx, min_node_idx, ArenaEdge::MIN);
                            }
                        }
                    }
                }
            }

            if let Ok(Some(range_max)) = cvar_node.range_max(graph_backend) {
                // println!(" range max: {:?}", range_max);
                match range_max {
                    Elem::Arena(arena_idx) => {
                        // Make a direct edge to the arena node
                        // println!("  arena idx: {}", arena_idx);
                        if let Some(&max_node_idx) = arena_idx_to_node_idx.get(&arena_idx) {
                            graph.add_edge(node_idx, max_node_idx, ArenaEdge::MAX);
                        }
                    }
                    _ => {
                        // attempt to find the elem in our `inner` and get the associated arena_graph index
                        let max_arena_idx = self
                            .inner
                            .iter()
                            .find(|(_, elem)| elem == &range_max)
                            .map(|(idx, _)| *idx);
                        // Add edges to the min arena indices
                        if let Some(max_idx) = max_arena_idx {
                            // println!("  max idx: {:?}", max_idx);
                            if let Some(&max_node_idx) = arena_idx_to_node_idx.get(&max_idx) {
                                // println!("   max node idx: {:?}", max_node_idx);
                                graph.add_edge(node_idx, max_node_idx, ArenaEdge::MAX);
                            }
                        }
                    }
                }
            }
        }

        // Ensure the graph does not have a cycle
        // debug_assert!(
        //     !petgraph::algo::is_cyclic_directed(&graph),
        //     "The graph contains a cycle!"
        // );

        graph
    }
}

pub fn mermaid_str(graph: &Graph<ArenaNode, ArenaEdge, Directed, usize>) -> String {
    let mut mermaid_str = Vec::new();
    // let raw_start_str = "flowchart TB\n";
    let raw_start_str = r#"
%%{
init : {
'theme': 'base',
'themeVariables': {
  'primaryColor': '#1a1b26',
  'primaryTextColor': '#d5daf0',
  'primaryBorderColor': '#4c4c4c',
  'lineColor': '#414868',
  'secondaryColor': '#24283b',
  'tertiaryColor': '#24283b'
},
"flowchart" : {
  "defaultRenderer": "elk"
}
}
}%%

flowchart TB
"#;
    mermaid_str.push(raw_start_str.to_string());

    let nodes_str = graph
        .node_indices()
        .map(|idx| arena_mermaid_node(graph, "\t", idx, true, true, None))
        .collect::<Vec<_>>()
        .join("\n");

    let edges_str = graph
        .edge_indices()
        .map(|edge| {
            let (from, to) = graph.edge_endpoints(edge).unwrap();
            let edge_label = format!("{}", graph[edge]);
            if edge_label.is_empty() {
                // don't do a label
                format!("    {} --> {}", from.index(), to.index(),)
            } else {
                // do an edge label
                format!(
                    "    {} -->|\"{}\"| {}",
                    from.index(),
                    edge_label,
                    to.index(),
                )
            }
        })
        .collect::<Vec<_>>()
        .join("\n");

    mermaid_str.push(nodes_str);
    mermaid_str.push(edges_str);

    // Make an invisible node that holds all our edge information for coloring later on frontend
    let data_str = graph
        .edge_indices()
        .map(|edge| {
            let (from, to) = graph.edge_endpoints(edge).unwrap();
            format!("LS-{}_LE-{}_{}", from.index(), to.index(), &graph[edge])
        })
        .collect::<Vec<_>>()
        .join(";")
        + " ";

    let invis_data = format!(
        "    {}(\"{}\"):::INVIS\n    classDef INVIS display:none",
        graph.node_count(),
        data_str
    );
    mermaid_str.push(invis_data);
    mermaid_str.join("\n")
}

pub fn arena_mermaid_node(
    graph: &Graph<ArenaNode, ArenaEdge, Directed, usize>,
    indent: &str,
    idx: NodeIdx,
    style: bool,
    _loc: bool,
    class: Option<&str>,
) -> String {
    let node = &graph[idx];
    let mut node_str = match node {
        ArenaNode::ARENA(arena_idx) => {
            format!("{indent}{}{{{{\"{}\"}}}}", idx.index(), arena_idx)
        }
        ArenaNode::ELEM(label) => {
            format!("{indent}{}(\"{}\")", idx.index(), label.replace('\"', "'"))
        }
        ArenaNode::CVAR(label) => {
            format!("{indent}{}(\"{}\")", idx.index(), label.replace('\"', "'"))
        }
    };

    if style {
        node_str.push_str(&format!(
            "\n{indent}style {} fill:{}",
            idx.index(),
            node.dot_str_color()
        ));
    }

    if let Some(class) = class {
        node_str.push_str(&format!("\n{indent}class {} {class}", idx.index(),));
    }

    node_str
}

fn _calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

impl GraphBackend for Analyzer {}

impl GraphDot for Analyzer {
    fn cluster_str(
        &self,
        arena: &mut RangeArena<Elem<Concrete>>,
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

        let mut struct_parts = children
            .iter()
            .filter(|child| {
                if matches!(g.node(**child), Node::ContextVar(..)) {
                    ContextVarNode::from(**child).is_struct(g).unwrap_or(false)
                } else {
                    false
                }
            })
            .copied()
            .collect::<BTreeSet<NodeIdx>>();
        let strukt_children = struct_parts
            .iter()
            .flat_map(|strukt| {
                g.children_exclude(*strukt, 0, &[Edge::Context(ContextEdge::Subcontext)])
            })
            .collect::<BTreeSet<NodeIdx>>();
        struct_parts.extend(strukt_children);

        let edges_for_structs = g
            .edges_for_nodes(&struct_parts)
            .into_iter()
            .filter(|(_, _, e, _)| *e != Edge::Context(ContextEdge::InputVariable))
            .collect::<BTreeSet<_>>();
        children_edges.extend(edges_for_structs);

        let preindent = " ".repeat(4 * depth.saturating_sub(1));
        let indent = " ".repeat(4 * depth);
        let child_node_str = children
            .iter()
            .filter_map(|child| {
                if handled_nodes.lock().unwrap().contains(child) {
                    return None;
                }

                if handled_nodes.lock().unwrap().contains(child) {
                    return None;
                }

                let post_str = match self.node(*child) {
                    Node::Context(c) => {
                        *cluster_num += 2;
                        if let Some(inner) = self.cluster_str(
                            arena,
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
                            arena,
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
                            arena,
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
                            arena,
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
                                if !handled_nodes.lock().unwrap().contains(child) {
                                    handled_nodes.lock().unwrap().insert(*child);
                                }
                                mermaid_node(
                                    self,
                                    arena,
                                    &indent,
                                    *child,
                                    true,
                                    true,
                                    Some(&curr_cluster_name),
                                )
                            })
                            .collect::<Vec<_>>()
                            .join("\n")
                    }
                    _ => "".to_string(),
                };

                if as_mermaid {
                    if handled_nodes.lock().unwrap().contains(child) {
                        return if !post_str.is_empty() {
                            Some(post_str)
                        } else {
                            None
                        };
                    } else {
                        handled_nodes.lock().unwrap().insert(*child);
                    }
                    Some(format!(
                        "{}\n{indent}{post_str}",
                        mermaid_node(
                            self,
                            arena,
                            &indent,
                            *child,
                            true,
                            true,
                            Some(&curr_cluster_name),
                        )
                    ))
                } else {
                    {
                        if handled_nodes.lock().unwrap().contains(child) {
                            return None;
                        } else {
                            handled_nodes.lock().unwrap().insert(*child);
                        }
                    }
                    Some(format!(
                        "{indent}{} [label = \"{}\", color = \"{}\"]\n{}",
                        petgraph::graph::GraphIndex::index(child),
                        as_dot_str(*child, g, arena).replace('\"', "\'"),
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
                    mermaid_node(
                        self,
                        arena,
                        &indent,
                        node,
                        true,
                        true,
                        Some(&curr_cluster_name),
                    )
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
                "{preindent}subgraph cluster_{} {{\n{indent}{}\n{indent}{} [label = \"{}\", color = \"{}\"]\n{}\n{}\n}}",
                cluster_num,
                if is_killed && curr_cluster % 2 == 0 {
                    "bgcolor=\"#7a0b0b\""
                } else if is_killed {
                    "bgcolor=\"#e04646\""
                } else if curr_cluster % 2 == 0 {
                    "bgcolor=\"#545e87\""
                } else {
                    "bgcolor=\"#1a1b26\""
                },
                node.index(),
                as_dot_str(node, g, arena).replace('\"', "\'"),
                self.node(node).dot_str_color(),
                child_node_str,
                edge_str,
            ))
        }
    }

    fn dot_str(&self, arena: &mut RangeArena<Elem<Concrete>>) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerBackend,
    {
        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26"; rankdir="BT"; splines=ortho; size="6,6"; ratio="fill";layout="fdp";"##;
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
                                arena,
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
                            as_dot_str(*node, self, arena).replace('\"', "\'"),
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

    fn dot_str_no_tmps(&self, arena: &mut RangeArena<Elem<Concrete>>) -> String
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
            bgcolor="#1a1b26"; rankdir="BT"; splines=ortho; size="6,6"; ratio="fill";layout="fdp";"##;
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
                                r.as_dot_str(self, &mut arena.clone())
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
                        _ => as_dot_str(idx, &G { graph: &new_graph }, &mut arena.clone()),
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

    fn mermaid_str(&self, arena: &mut RangeArena<Elem<Concrete>>) -> String
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
                                arena,
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
                                as_dot_str(*node, self, arena).replace('\"', "\'"),
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

    fn mark_dirty(&mut self, _node: NodeIdx) {}
    fn dirty_nodes(&self) -> &BTreeSet<NodeIdx> {
        panic!("Should not call this")
    }

    fn dirty_nodes_mut(&mut self) -> &mut BTreeSet<NodeIdx> {
        panic!("Should not call this")
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        self.graph
    }
}

impl GraphDot for G<'_> {
    fn cluster_str(
        &self,
        _arena: &mut RangeArena<<Self as GraphLike>::RangeElem>,
        _node: NodeIdx,
        _cluster_num: &mut usize,
        _is_killed: bool,
        _handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
        _handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
        _depth: usize,
        _as_mermaid: bool,
    ) -> Option<String>
    where
        Self: std::marker::Sized,
    {
        todo!()
    }

    fn dot_str(&self, _arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: shared::AnalyzerLike,
    {
        todo!()
    }

    fn dot_str_no_tmps(&self, _arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: GraphLike + shared::AnalyzerLike,
    {
        todo!()
    }

    fn mermaid_str(&self, _arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: shared::AnalyzerLike,
    {
        todo!()
    }
}

impl GraphBackend for G<'_> {}

pub fn mermaid_node(
    g: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
    indent: &str,
    node: NodeIdx,
    style: bool,
    loc: bool,
    class: Option<&str>,
) -> String {
    let mut node_str = format!(
        "{indent}{}(\"{}\")",
        petgraph::graph::GraphIndex::index(&node),
        as_dot_str(node, g, arena).replace('\"', "\'"),
    );

    if style {
        node_str.push_str(&format!(
            "\n{indent}style {} stroke:{}",
            petgraph::graph::GraphIndex::index(&node),
            g.node(node).dot_str_color()
        ));
    }

    if loc {
        let current_node = node;
        match g.node(current_node) {
            Node::ContextVar(..) => {
                // highlight self
                if let Ok(solang_parser::pt::Loc::File(f, s, e)) =
                    graph::nodes::ContextVarNode::from(current_node).loc(g)
                {
                    node_str.push_str(&format!(
                        "\n{indent}class {} loc_{f}_{s}_{e}",
                        petgraph::graph::GraphIndex::index(&current_node)
                    ));
                }

                // color the forks
                if let Some(ctx_node) =
                    graph::nodes::ContextVarNode::from(current_node).maybe_ctx(g)
                {
                    gather_context_info(g, indent, ctx_node, current_node, &mut node_str);
                }
            }
            Node::Context(ctx) => {
                // highlight self
                if let solang_parser::pt::Loc::File(f, s, e) = ctx.loc {
                    node_str.push_str(&format!(
                        "\n{indent}class {} loc_{f}_{s}_{e}",
                        petgraph::graph::GraphIndex::index(&current_node)
                    ));
                }

                // color the forks
                let ctx_node = graph::nodes::ContextNode::from(current_node);
                gather_context_info(g, indent, ctx_node, current_node, &mut node_str);
            }
            _ => {}
        }
    }

    if let Some(class) = class {
        node_str.push_str(&format!(
            "\n{indent}class {} {class}",
            petgraph::graph::GraphIndex::index(&node),
        ));
    }

    node_str
}

fn gather_context_info(
    g: &impl GraphBackend,
    indent: &str,
    mut ctx_node: ContextNode,
    original_cvar_node: NodeIdx,
    node_str: &mut String,
) {
    loop {
        let mut found_continue = false;
        let current_loc = ctx_node.underlying(g).unwrap().loc;
        for edge in g
            .graph()
            .edges_directed(ctx_node.into(), Direction::Outgoing)
        {
            if let Edge::Context(ContextEdge::Continue(true_or_false)) = edge.weight() {
                let target_node = edge.target();
                if let Node::Context(_ctx) = g.node(target_node) {
                    // error!("found continue pointing to node");
                    ctx_node = target_node.into();
                    found_continue = true;
                    // Gather the edge weight and the loc of the Context node it points to
                    if let solang_parser::pt::Loc::File(f, s, e) = current_loc {
                        let fork_str = format!(
                            "\n{indent}class {} fork_{f}_{s}_{e}_{}",
                            petgraph::graph::GraphIndex::index(&original_cvar_node),
                            match *true_or_false {
                                "fork_true" => true,
                                "fork_false" => false,
                                _ => false,
                            }
                        );
                        // error!("in gather_context_info, {:?}", fork_str);
                        node_str.push_str(&fork_str);
                    }
                    break;
                }
            }
        }
        if !found_continue {
            break;
        }
    }
}
