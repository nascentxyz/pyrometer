use crate::{AnalyzerLike, Heirarchical};

use ahash::AHashMap;
use petgraph::{
    graph::{EdgeIndex, Graph, NodeIndex},
    Directed,
};

use std::{
    collections::BTreeSet,
    hash::Hash,
    sync::{Arc, Mutex},
};

use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::runtime::Runtime;
use tracing::{error, trace};

pub static mut USE_DEBUG_SITE: bool = false;

pub type NodeIdx = NodeIndex<usize>;
pub type EdgeIdx = EdgeIndex<usize>;
pub type RangeArenaIdx = usize;

#[derive(Default, Clone, Debug)]
pub struct RangeArena<T: Hash> {
    pub ranges: Vec<T>,
    pub map: AHashMap<T, usize>,
}

/// A trait that constructs dot-like visualization strings (either mermaid or graphviz)
pub trait GraphLike {
    type Node;
    type Edge: Ord + PartialEq + Heirarchical + Copy;
    type RangeElem: Hash + PartialEq + Eq + PartialOrd + Clone + std::fmt::Display + Default;
    /// Get a mutable reference to the graph
    fn graph_mut(&mut self) -> &mut Graph<Self::Node, Self::Edge, Directed, usize>;
    /// Get a reference to the graph
    fn graph(&self) -> &Graph<Self::Node, Self::Edge, Directed, usize>;
    /// Add a node to the graph
    fn add_node(&mut self, node: impl Into<Self::Node>) -> NodeIdx {
        let res = self.graph_mut().add_node(node.into());
        // if res.index() == 219 {
        //     panic!("here");
        // }
        self.mark_dirty(res);
        res
    }
    /// Get a reference to a node in the graph
    fn node(&self, node: impl Into<NodeIdx>) -> &Self::Node {
        self.graph()
            .node_weight(node.into())
            .expect("Index not in graph")
    }
    /// Get a mutable reference to a node in the graph
    fn node_mut(&mut self, node: impl Into<NodeIdx>) -> &mut Self::Node {
        self.graph_mut()
            .node_weight_mut(node.into())
            .expect("Index not in graph")
    }

    fn mark_dirty(&mut self, node: NodeIdx);
    fn dirty_nodes(&self) -> &BTreeSet<NodeIdx>;
    fn dirty_nodes_mut(&mut self) -> &mut BTreeSet<NodeIdx>;
    fn take_dirty_nodes(&mut self) -> BTreeSet<NodeIdx> {
        std::mem::take(self.dirty_nodes_mut())
    }

    /// Add an edge to the graph
    fn add_edge(
        &mut self,
        from_node: impl Into<NodeIdx>,
        to_node: impl Into<NodeIdx>,
        edge: impl Into<Self::Edge>,
    ) {
        let from = from_node.into();
        let to = to_node.into();
        self.mark_dirty(from);
        self.mark_dirty(to);
        self.graph_mut().add_edge(from, to, edge.into());
    }
}

/// A trait that constructs dot-like visualization strings (either mermaid or graphviz)
pub trait GraphDot: GraphLike {
    /// Open a dot using graphviz
    fn open_dot(&self, arena: &mut RangeArena<<Self as GraphLike>::RangeElem>)
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
        file.write_all(self.dot_str(arena).as_bytes()).unwrap();
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

    fn open_mermaid(&self, arena: &mut RangeArena<<Self as GraphLike>::RangeElem>)
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike,
    {
        println!("Generating mermaid... This may take a moment");
        use std::env::temp_dir;
        use std::fs;
        use std::io::Write;
        use std::process::Command;
        let temp_dir = temp_dir();
        let file_name = "mermaid.mmd";
        let config_name = "mermaidConfig.json";
        let mut temp_path = temp_dir.clone();
        let mut temp_config_path = temp_dir.clone();
        temp_path.push(file_name);
        temp_config_path.push(config_name);

        let mut file = fs::File::create(temp_config_path.clone()).unwrap();
        file.write_all(include_bytes!("./mermaidConfig.json"))
            .unwrap();

        let temp_svg_filename: String = format!("{}/mermaid.svg", &temp_dir.to_string_lossy());

        let mut file = fs::File::create(temp_path.clone()).unwrap();
        file.write_all(self.mermaid_str(arena).as_bytes()).unwrap();
        Command::new("mmdc")
            .arg("-i")
            .arg(temp_path)
            .arg("-o")
            .arg(&temp_svg_filename)
            .arg("-c")
            .arg(temp_config_path)
            .arg("-b")
            .arg("#1a1b26")
            .output()
            .expect("You may need to install mermaid-cli (https://github.com/mermaid-js/mermaid-cli), check if command 'mmdc' is in your $PATH");
        println!("Done generating mermaid svg, opening...");
        Command::new("open")
            .arg(&temp_svg_filename)
            .spawn()
            .expect("failed to execute process");
    }

    /// Creates a subgraph for visually identifying contexts and subcontexts
    #[allow(clippy::too_many_arguments)]
    fn cluster_str(
        &self,
        arena: &mut RangeArena<<Self as GraphLike>::RangeElem>,
        node: NodeIdx,
        cluster_num: &mut usize,
        is_killed: bool,
        handled_nodes: Arc<Mutex<BTreeSet<NodeIdx>>>,
        handled_edges: Arc<Mutex<BTreeSet<EdgeIndex<usize>>>>,
        depth: usize,
        as_mermaid: bool,
    ) -> Option<String>
    where
        Self: std::marker::Sized;

    /// Constructs a dot string
    fn dot_str(&self, arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike;

    /// Construct a dot string while filtering temporary variables
    fn dot_str_no_tmps(&self, arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: GraphLike + AnalyzerLike;

    fn mermaid_str(&self, arena: &mut RangeArena<<Self as GraphLike>::RangeElem>) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike;
}

#[derive(Serialize, Deserialize, Debug)]
struct GraphMessage {
    graph: String,
    timestamp: u64,
}

pub fn post_to_site<G>(graph: &G, arena: &mut RangeArena<<G as GraphLike>::RangeElem>)
where
    G: GraphDot + AnalyzerLike,
{
    let rt = Runtime::new().unwrap();
    rt.block_on(async {
        post_to_site_async(graph, arena).await;
    });
}

async fn post_to_site_async<G>(graph: &G, arena: &mut RangeArena<<G as GraphLike>::RangeElem>)
where
    G: GraphDot + AnalyzerLike,
{
    let client = Client::new();
    let graph_msg = GraphMessage {
        graph: graph.mermaid_str(arena),
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("Time went backwards")
            .as_secs(),
    };

    let res = client
        .post("http://127.0.0.1:8545/addgraph")
        .json(&graph_msg)
        .send()
        .await
        .expect("Failed to send request");

    if res.status().is_success() {
        trace!("Successfully posted dot to site");
    } else {
        error!("Failed to post graph to site: {:?}", res.status());
    }
}
