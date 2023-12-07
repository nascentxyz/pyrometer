

pub trait AsDotStr {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String;
}

/// A trait that constructs dot-like visualization strings (either mermaid or graphviz)
pub trait GraphLike {
    /// Get a mutable reference to the graph
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize>;
    /// Get a reference to the graph
    fn graph(&self) -> &Graph<Node, Edge, Directed, usize>;
    /// Add a node to the graph
    fn add_node(&mut self, node: impl Into<Node>) -> NodeIdx {
        self.graph_mut().add_node(node.into())
    }
    /// Get a reference to a node in the graph
    fn node(&self, node: impl Into<NodeIdx>) -> &Node {
        self.graph()
            .node_weight(node.into())
            .expect("Index not in graph")
    }
    /// Get a mutable reference to a node in the graph
    fn node_mut(&mut self, node: impl Into<NodeIdx>) -> &mut Node {
        self.graph_mut()
            .node_weight_mut(node.into())
            .expect("Index not in graph")
    }
    /// Add an edge to the graph
    fn add_edge(
        &mut self,
        from_node: impl Into<NodeIdx>,
        to_node: impl Into<NodeIdx>,
        edge: impl Into<Edge>,
    ) {
        self.graph_mut()
            .add_edge(from_node.into(), to_node.into(), edge.into());
    }
}

impl<T: GraphLike> GraphDot for T {}

/// A trait that constructs dot-like visualization strings (either mermaid or graphviz)
pub trait GraphDot: GraphLike {
    /// Open a dot using graphviz
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

	/// Creates a subgraph for visually identifying contexts and subcontexts
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

    /// Constructs a dot string
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
                if !handled_nodes.lock().unwrap().contains(node) {
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
                if !handled_edges.lock().unwrap().contains(&edge) {
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

    /// Construct a dot string while filtering temporary variables
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