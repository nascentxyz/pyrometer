#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    pub fn join(
        &self,
        _func: FunctionNode,
        _mapping: &BTreeMap<ContextVarNode, FunctionParamNode>,
        _analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        todo!("Joining not supported yet");
    }

    pub fn total_width(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<usize, GraphError> {
        self.first_ancestor(analyzer)?
            .number_of_live_edges(analyzer)
    }

    pub fn depth(&self, analyzer: &impl GraphLike) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut (impl GraphLike + AnalyzerLike),
    ) -> Result<&'a mut Context, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Context, GraphError> {
        match analyzer.node(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<(Loc, KilledKind)>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?
            .ret
            .push((ret_stmt_loc, Some(ret)));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    pub fn add_empty_return(
        &self,
        ret_stmt_loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?
            .ret
            .push((ret_stmt_loc, None));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    pub fn propogate_end(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying = &mut self.underlying_mut(analyzer)?;
        let curr_live = underlying.number_of_live_edges;
        underlying.number_of_live_edges = 0;
        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            let live_edges = &mut parent.underlying_mut(analyzer)?.number_of_live_edges;
            *live_edges = live_edges.saturating_sub(1 + curr_live);
            parent.propogate_end(analyzer)?;
        }
        Ok(())
    }

    pub fn return_nodes(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        let rets = &self.underlying(analyzer)?.ret.clone();
        let all_good = rets.iter().all(|(_, node)| node.is_some());
        if all_good {
            Ok(rets
                .iter()
                .map(|(loc, node)| (*loc, node.unwrap()))
                .collect())
        } else {
            Ok(vec![])
        }
    }

    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }

    pub fn deps_dag(&self, g: &impl GraphLike) -> Result<(), GraphError> {
        let deps = self.ctx_deps(g)?;
        // #[derive(Debug, Copy, Clone)]
        // pub enum DepEdge {
        //     Lhs,
        //     Rhs,
        // }

        let mut gr: petgraph::Graph<NodeIdx, RangeOp, petgraph::Directed, usize> =
            petgraph::Graph::default();

        let mut contains: BTreeMap<ContextVarNode, petgraph::graph::NodeIndex<usize>> =
            BTreeMap::default();
        deps.iter().try_for_each(|dep| {
            let mapping = dep.graph_dependent_on(g)?;
            mapping.into_iter().for_each(|(_k, tmp)| {
                if let Some(rhs) = tmp.rhs {
                    let lhs = if let Some(ver) = contains.keys().find(|other| {
                        other.range(g).unwrap() == tmp.lhs.range(g).unwrap()
                            && tmp.lhs.display_name(g).unwrap() == other.display_name(g).unwrap()
                    }) {
                        *contains.get(ver).unwrap()
                    } else {
                        let lhs = gr.add_node(tmp.lhs.into());
                        contains.insert(tmp.lhs, lhs);
                        lhs
                    };

                    let new_rhs = if let Some(ver) = contains.keys().find(|other| {
                        other.range(g).unwrap() == rhs.range(g).unwrap()
                            && rhs.display_name(g).unwrap() == other.display_name(g).unwrap()
                    }) {
                        *contains.get(ver).unwrap()
                    } else {
                        let new_rhs = gr.add_node(rhs.into());
                        contains.insert(rhs, new_rhs);
                        new_rhs
                    };
                    gr.add_edge(lhs, new_rhs, tmp.op);
                }
            });
            Ok(())
        })?;

        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());
        let nodes_and_edges_str = format!(
            "{:?}",
            Dot::with_attr_getters(
                &gr,
                &[
                    petgraph::dot::Config::GraphContentOnly,
                    petgraph::dot::Config::NodeNoLabel,
                    petgraph::dot::Config::EdgeNoLabel
                ],
                &|_graph, edge_ref| {
                    let e = edge_ref.weight();
                    format!("label = \"{e:?}\"")
                },
                &|_graph, (idx, node_ref)| {
                    let inner = match g.node(*node_ref) {
                        Node::ContextVar(cvar) => {
                            let range_str = if let Some(r) = cvar.ty.ref_range(g).unwrap() {
                                r.as_dot_str(g)
                                // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(g).unwrap(),
                                range_str
                            )
                        }
                        _ => as_dot_str(idx, g),
                    };
                    format!(
                        "label = \"{}\", color = \"{}\"",
                        inner.replace('\"', "\'"),
                        g.node(*node_ref).dot_str_color()
                    )
                }
            )
        );
        dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        let dot_str = dot_str.join("\n");

        println!("{dot_str}");
        use std::env::temp_dir;
        use std::fs;
        use std::io::Write;
        use std::process::Command;
        let mut dir = temp_dir();
        let file_name = "dot.dot";
        dir.push(file_name);

        let mut file = fs::File::create(dir.clone()).unwrap();
        file.write_all(dot_str.as_bytes()).unwrap();
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
        Ok(())
    }
}

impl From<ContextNode> for NodeIdx {
    fn from(val: ContextNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}