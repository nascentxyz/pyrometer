use crate::GraphError;
use shared::{AnalyzerLike, GraphLike};

impl ContextNode {
	/// Use a Difference Logic solver to see if it is unreachable
	pub fn unreachable(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let mut solver = self.dl_solver(analyzer)?.clone();
        match solver.solve_partial(analyzer)? {
            SolveStatus::Unsat => Ok(true),
            _ => Ok(false),
        }
    }

    /// Get the dependencies as normalized solver atoms
    pub fn dep_atoms(&self, analyzer: &impl GraphLike) -> Result<Vec<SolverAtom>, GraphError> {
        let deps: Vec<_> = self.ctx_deps(analyzer)?;
        let mut ranges = BTreeMap::default();
        deps.iter().try_for_each(|dep| {
            let range = dep.ref_range(analyzer)?.unwrap();
            if range.unsat(analyzer) {
                panic!(
                    "initial range for {} not sat",
                    dep.display_name(analyzer).unwrap()
                );
            }
            let r = range.into_flattened_range(analyzer)?;
            // println!("dep {} range: [{}, {}]", dep.display_name(analyzer).unwrap(), r.min, r.max);
            ranges.insert(*dep, r);
            Ok(())
        })?;

        Ok(ranges
            .iter()
            .filter_map(|(_dep, range)| {
                if let Some(atom) = range.min.atomize() {
                    // println!("dep {} atomized min: {:?}", dep.display_name(analyzer).unwrap(), atom);
                    Some(atom)
                } else {
                    // println!("dep {} atomized max: {:?}", dep.display_name(analyzer).unwrap(), atom);
                    range.max.atomize()
                }
            })
            .collect::<Vec<SolverAtom>>())
    }

    /// Get the difference logic solver associated with this context
    pub fn dl_solver<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a DLSolver, GraphError> {
        Ok(&self.underlying(analyzer)?.dl_solver)
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(&self, analyzer: &impl GraphLike) -> Result<Vec<ContextVarNode>, GraphError> {
        Ok(self.underlying(analyzer)?.ctx_deps.clone())
    }

    /// Adds a dependency for this context to exit successfully
    pub fn add_ctx_dep(
        &self,
        dep: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        tracing::trace!("Adding ctx dependency: {}", dep.display_name(analyzer)?);
        if dep.is_controllable(analyzer)? {
            let range = dep.ref_range(analyzer)?.unwrap();
            let r = range.into_flattened_range(analyzer)?;
            let underlying = self.underlying_mut(analyzer)?;
            if !underlying.ctx_deps.contains(&dep) {
                // add the atomic constraint
                if let Some(atom) = r.min.atomize() {
                    underlying.dl_solver.add_constraints(vec![atom]);
                } else if let Some(atom) = r.max.atomize() {
                    underlying.dl_solver.add_constraints(vec![atom]);
                }

                underlying.ctx_deps.push(dep);
            }
        }
        Ok(())
    }

        /// Creates a DAG of the context dependencies and opens it with graphviz
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