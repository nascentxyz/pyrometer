

impl ContextNode {
	pub fn unreachable(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let mut solver = self.dl_solver(analyzer)?.clone();
        match solver.solve_partial(analyzer)? {
            SolveStatus::Unsat => Ok(true),
            _ => Ok(false),
        }
    }

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

    pub fn dl_solver<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a DLSolver, GraphError> {
        Ok(&self.underlying(analyzer)?.dl_solver)
    }

    pub fn dep_graph(&self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        let deps = self.ctx_deps(analyzer)?;
        println!("{}:\n", self.path(analyzer));
        deps.iter().try_for_each(|dep| {
            let t = dep.graph_dependent_on(analyzer)?;
            println!("{:#?}", t);
            Ok::<(), GraphError>(())
        })?;
        Ok(())
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(&self, analyzer: &impl GraphLike) -> Result<Vec<ContextVarNode>, GraphError> {
        Ok(self.underlying(analyzer)?.ctx_deps.clone())
    }

    pub fn ctx_deps_as_controllables_str(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<String>, GraphError> {
        let deps: Vec<_> = self.ctx_deps(analyzer)?.into_iter().collect();
        println!("here: {}, {}", deps.len(), self.ctx_deps(analyzer)?.len());
        fn decompose(
            dep: ContextVarNode,
            acc: &mut String,
            analyzer: &impl GraphLike,
        ) -> Result<(), GraphError> {
            println!("acc: {acc}");
            if let Ok(Some(tmp)) = dep.tmp_of(analyzer) {
                decompose(tmp.lhs, acc, analyzer)?;
                *acc = acc.to_owned() + &tmp.op.to_string();
                if let Some(rhs) = tmp.rhs {
                    decompose(rhs, acc, analyzer)?;
                }
            } else {
                *acc = acc.to_owned() + &dep.display_name(analyzer)?;
            }
            Ok(())
        }

        deps.iter()
            .map(|dep| {
                let mut t = "".to_string();
                decompose(*dep, &mut t, analyzer)?;
                Ok(t)
            })
            .collect::<Result<Vec<String>, _>>()
    }

    pub fn flat_ctx_deps(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        fn decompose(
            dep: ContextVarNode,
            analyzer: &impl GraphLike,
        ) -> Result<Vec<ContextVarNode>, GraphError> {
            println!("decomposing: {}", dep.display_name(analyzer).unwrap());
            let mut top_level_deps = vec![];
            if let Ok(Some(tmp)) = dep.tmp_of(analyzer) {
                if dep.is_controllable(analyzer)? {
                    if let Some(rhs) = tmp.rhs {
                        top_level_deps.extend(decompose(rhs, analyzer)?);
                    }
                    top_level_deps.extend(decompose(tmp.lhs, analyzer)?);
                    println!("{} is controllable", dep.display_name(analyzer).unwrap());
                    top_level_deps.push(dep);
                }
            } else if dep.is_controllable(analyzer)? {
                println!(
                    "atomic {} is controllable",
                    dep.display_name(analyzer).unwrap()
                );
                top_level_deps.push(dep);
            }

            Ok(top_level_deps)
        }

        Ok(self
            .ctx_deps(analyzer)?
            .into_iter()
            .map(|dep| decompose(dep, analyzer))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect())
    }

    pub fn ctx_dep_ranges(&self, analyzer: &impl GraphLike) -> Result<Vec<SolcRange>, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .ctx_deps
            .clone()
            .into_iter()
            .flat_map(|dep| {
                let tmp = dep.tmp_of(analyzer).unwrap().unwrap();
                if let Some(rhs) = tmp.rhs {
                    println!("dep lhs: {}", tmp.lhs.display_name(analyzer).unwrap());
                    println!("dep rhs: {}", rhs.display_name(analyzer).unwrap());
                    vec![
                        tmp.lhs
                            .ref_range(analyzer)
                            .unwrap()
                            .unwrap()
                            .into_flattened_range(analyzer)
                            .unwrap(),
                        rhs.ref_range(analyzer)
                            .unwrap()
                            .unwrap()
                            .into_flattened_range(analyzer)
                            .unwrap(),
                    ]
                } else {
                    println!("dep lhs: {}", tmp.lhs.display_name(analyzer).unwrap());
                    vec![tmp
                        .lhs
                        .ref_range(analyzer)
                        .unwrap()
                        .unwrap()
                        .into_flattened_range(analyzer)
                        .unwrap()]
                }
            })
            .collect())
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
}