use crate::AnalyzerLike;
use crate::Heirarchical;

use petgraph::{
    graph::{EdgeIndex, Graph, NodeIndex},
    Directed,
};
use std::{
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

pub type NodeIdx = NodeIndex<usize>;
pub type EdgeIdx = EdgeIndex<usize>;
pub type RangeArenaIdx = usize;

#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct RangeArena<T> {
    pub ranges: Vec<T>,
}

/// A trait that constructs dot-like visualization strings (either mermaid or graphviz)
pub trait GraphLike {
    type Node;
    type Edge: Ord + PartialEq + Heirarchical + Copy;
    type RangeElem: PartialEq;
    /// Get a mutable reference to the graph
    fn graph_mut(&mut self) -> &mut Graph<Self::Node, Self::Edge, Directed, usize>;
    /// Get a reference to the graph
    fn graph(&self) -> &Graph<Self::Node, Self::Edge, Directed, usize>;
    /// Add a node to the graph
    fn add_node(&mut self, node: impl Into<Self::Node>) -> NodeIdx {
        let res = self.graph_mut().add_node(node.into());
        // if res == 81.into() {
        //     panic!("here");
        // } else {
        //     res
        // }
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
    /// Add an edge to the graph
    fn add_edge(
        &mut self,
        from_node: impl Into<NodeIdx>,
        to_node: impl Into<NodeIdx>,
        edge: impl Into<Self::Edge>,
    ) {
        self.graph_mut()
            .add_edge(from_node.into(), to_node.into(), edge.into());
    }

    fn range_arena(&self) -> &RangeArena<Self::RangeElem>;
    fn range_arena_mut(&mut self) -> &mut RangeArena<Self::RangeElem>;

    fn range_arena_idx(&self, elem: &Self::RangeElem) -> Option<usize> {
        self.range_arena().ranges.iter().position(|r| r == elem)
    }

    fn range_arena_idx_or_upsert(&mut self, elem: Self::RangeElem) -> usize {
        if let Some(idx) = self.range_arena_idx(&elem) {
            idx
        } else {
            let idx = self.range_arena().ranges.len();
            self.range_arena_mut().ranges.push(elem);
            idx
        }
    }
}

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

    fn open_mermaid(&self)
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
        file.write_all(self.mermaid_str().as_bytes()).unwrap();
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
        Self: std::marker::Sized;

    /// Constructs a dot string
    fn dot_str(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike;

    /// Construct a dot string while filtering temporary variables
    fn dot_str_no_tmps(&self) -> String
    where
        Self: std::marker::Sized,
        Self: GraphLike + AnalyzerLike;

    fn mermaid_str(&self) -> String
    where
        Self: std::marker::Sized,
        Self: AnalyzerLike;
}
