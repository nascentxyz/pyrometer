use crate::FlattenedRange;
use crate::elem::Elem;
use crate::SolcRange;
use crate::{
    as_dot_str,
    nodes::{ContextNode, ContextVarNode},
    range::{elem::RangeOp, Range, RangeEval},
    solvers::{
        dl::{DLSolver, SolveStatus},
        Atomize, SolverAtom,
    },
    AnalyzerBackend, AsDotStr, GraphBackend, GraphError, Node,
};
use std::borrow::Cow;

use shared::NodeIdx;

use petgraph::dot::Dot;

use std::collections::BTreeMap;

impl ContextNode {
    /// Use a Difference Logic solver to see if it is unreachable
    pub fn unreachable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let mut solver = self.dl_solver(analyzer)?.clone();
        match solver.solve_partial(analyzer)? {
            SolveStatus::Unsat => Ok(true),
            _ => Ok(false),
        }
    }

    /// Get the dependencies as normalized solver atoms
    pub fn dep_atoms(&self, analyzer: &mut impl GraphBackend) -> Result<Vec<SolverAtom>, GraphError> {
        let deps: Vec<_> = self.ctx_deps(analyzer)?;
        let mut ranges = BTreeMap::default();
        deps.iter().try_for_each(|dep| {
            let mut range = dep.range(analyzer)?.unwrap();
            let r: Cow<'_, _> = range.flattened_range(analyzer)?;
            ranges.insert(*dep, r.into_owned());
            Ok(())
        })?;

        Ok(ranges
            .iter()
            .filter_map(|(_dep, range)| {
                if let Some(atom) = Elem::Arena(range.min).atomize(analyzer) {
                    Some(atom)
                } else {
                    Elem::Arena(range.max).atomize(analyzer)
                }
            })
            .collect::<Vec<SolverAtom>>())
    }

    /// Get the difference logic solver associated with this context
    pub fn dl_solver<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a DLSolver, GraphError> {
        Ok(&self.underlying(analyzer)?.dl_solver)
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let deps = self
            .underlying(analyzer)?
            .ctx_deps
            .clone()
            .into_iter()
            .collect::<Vec<_>>();
        Ok(deps)
    }

    /// Adds a dependency for this context to exit successfully
    pub fn add_ctx_dep(
        &self,
        dep: ContextVarNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        tracing::trace!(
            "Adding ctx dependency: {}, is_controllable: {}",
            dep.display_name(analyzer)?,
            dep.is_controllable(analyzer)?
        );
        if dep.is_controllable(analyzer)? {
            // let underlying = self.underlying_mut(analyzer)?;
            if !self.underlying(analyzer)?.ctx_deps.contains(&dep) {
                // dep.cache_flattened_range(analyzer)?;
                let mut range = dep.range(analyzer)?.unwrap();
                let r = range.flattened_range(analyzer)?.into_owned();
                tracing::trace!("flattened: {}", <FlattenedRange as Into<SolcRange>>::into(r.clone()).as_dot_str(analyzer));
                // add the atomic constraint
                if let Some(atom) = Elem::Arena(r.min).atomize(analyzer) {
                    let mut solver = std::mem::take(&mut self.underlying_mut(analyzer)?.dl_solver);
                    solver.add_constraints(vec![atom], analyzer);
                    self.underlying_mut(analyzer)?.dl_solver = solver;
                } else if let Some(atom) = Elem::Arena(r.max).atomize(analyzer) {
                    let mut solver = std::mem::take(&mut self.underlying_mut(analyzer)?.dl_solver);
                    solver.add_constraints(vec![atom], analyzer);
                    self.underlying_mut(analyzer)?.dl_solver = solver;
                }

                let underlying = self.underlying_mut(analyzer)?;
                underlying.ctx_deps.insert(dep);
            }
        }
        Ok(())
    }

    /// Creates a DAG of the context dependencies and opens it with graphviz
    pub fn deps_dag(&self, g: &impl GraphBackend) -> Result<(), GraphError> {
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
                        other.ref_range(g).unwrap() == tmp.lhs.ref_range(g).unwrap()
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
