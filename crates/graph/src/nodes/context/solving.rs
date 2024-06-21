use crate::elem::Elem;

use crate::{
    nodes::{Concrete, ContextNode, ContextVarNode},
    range::Range,
    solvers::{
        dl::{DLSolver, SolveStatus},
        Atomize, SolverAtom,
    },
    AnalyzerBackend, GraphBackend, GraphError,
};
use std::borrow::Cow;

use shared::RangeArena;

use std::collections::BTreeMap;

impl ContextNode {
    /// Use a Difference Logic solver to see if it is unreachable
    pub fn unreachable(
        &self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        // println!("checking unreachable: {}", self.path(analyzer));
        let mut solver = self.dl_solver(analyzer)?.clone();
        match solver.solve_partial(analyzer, arena)? {
            SolveStatus::Unsat => {
                tracing::trace!("{} is unreachable via UNSAT", self.path(analyzer));
                Ok(true)
            }
            _e => {
                // println!("other: {e:?}");
                Ok(false)
            }
        }
    }

    /// Get the dependencies as normalized solver atoms
    pub fn dep_atoms(
        &self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<SolverAtom>, GraphError> {
        let deps: Vec<_> = self.ctx_deps(analyzer)?;
        let mut ranges = BTreeMap::default();
        deps.iter().try_for_each(|dep| {
            let mut range = dep.range(analyzer)?.unwrap();
            let r: Cow<'_, _> = range.flattened_range(analyzer, arena)?;
            ranges.insert(*dep, r.into_owned());
            Ok(())
        })?;

        Ok(ranges
            .iter()
            .filter_map(|(_dep, range)| {
                if let Some(atom) = Elem::Arena(range.min).atomize(analyzer, arena) {
                    Some(atom)
                } else {
                    Elem::Arena(range.max).atomize(analyzer, arena)
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

    pub fn debug_ctx_deps(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let deps = self.ctx_deps(analyzer)?;
        deps.iter().enumerate().for_each(|(i, var)| {
            println!(
                "{i}. {}",
                var.as_controllable_name(analyzer, arena).unwrap()
            )
        });
        Ok(())
    }

    /// Adds a dependency for this context to exit successfully
    pub fn add_ctx_dep(
        &self,
        dep: ContextVarNode,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        tracing::trace!(
            "Adding ctx ({}) dependency: {}, is_controllable: {}",
            self.path(analyzer),
            dep.display_name(analyzer)?,
            dep.is_controllable(analyzer)?
        );
        if dep.is_controllable(analyzer)? {
            // let underlying = self.underlying_mut(analyzer)?;
            if !self.underlying(analyzer)?.ctx_deps.contains(&dep) {
                // dep.cache_flattened_range(analyzer)?;
                let mut range = dep.range(analyzer)?.unwrap();

                let min = range.simplified_range_min(analyzer, arena)?;
                let max = range.simplified_range_max(analyzer, arena)?;

                let true_elem = Elem::from(true);
                let trivial_sat = min == true_elem && max == true_elem;
                if trivial_sat || min == Elem::Null || max == Elem::Null {
                    return Ok(());
                }

                let r = range.flattened_range(analyzer, arena)?.into_owned();

                // add the atomic constraint
                if let Some(atom) = Elem::Arena(r.min).atomize(analyzer, arena) {
                    let mut solver = std::mem::take(&mut self.underlying_mut(analyzer)?.dl_solver);
                    let constraints = solver.add_constraints(vec![atom], analyzer, arena);
                    constraints
                        .into_iter()
                        .for_each(|(constraint, normalized)| {
                            solver.add_constraint(constraint, normalized);
                        });
                    self.underlying_mut(analyzer)?.dl_solver = solver;
                } else if let Some(atom) = Elem::Arena(r.max).atomize(analyzer, arena) {
                    let mut solver = std::mem::take(&mut self.underlying_mut(analyzer)?.dl_solver);
                    let constraints = solver.add_constraints(vec![atom], analyzer, arena);
                    constraints
                        .into_iter()
                        .for_each(|(constraint, normalized)| {
                            solver.add_constraint(constraint, normalized);
                        });
                    self.underlying_mut(analyzer)?.dl_solver = solver;
                }

                let underlying = self.underlying_mut(analyzer)?;
                underlying.ctx_deps.insert(dep);
            }
        }
        Ok(())
    }
}
