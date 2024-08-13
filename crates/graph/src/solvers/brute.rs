use crate::{
    elem::{Elem, RangeElem},
    nodes::{Concrete, ContextVarNode, VarNode},
    solvers::{
        dl::{DLSolver, SolveStatus},
        Atomize, SolverAtom,
    },
    AnalyzerBackend, GraphBackend, Range, RangeEval, SolcRange,
};

use shared::{GraphError, RangeArena};

use alloy_primitives::U256;
use std::collections::BTreeMap;

pub trait SolcSolver {
    fn simplify(&mut self, analyzer: &impl AnalyzerBackend, arena: &mut RangeArena<Elem<Concrete>>);
    fn solve(
        &mut self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<AtomicSolveStatus, GraphError>;
    fn recurse_check(
        &mut self,
        idx: usize,
        solved_atomics: &mut Vec<usize>,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError>;
    fn check(
        &mut self,
        solved_for: usize,
        lmr: (Elem<Concrete>, Elem<Concrete>, Elem<Concrete>),
        solved_atomics: &mut Vec<usize>,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(bool, Option<HintOrRanges>), GraphError>;
}

pub enum AtomicSolveStatus {
    Unsat,
    Sat(AtomicSolveMap),
    Indeterminate,
}

pub type AtomicSolveMap = BTreeMap<Atomic, Concrete>;

#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct Atomic {
    pub idxs: Vec<ContextVarNode>,
}

#[derive(Clone, Debug)]
pub struct BruteBinSearchSolver {
    pub deps: Vec<ContextVarNode>,
    pub solves: BTreeMap<Atomic, Elem<Concrete>>,
    pub atomics: Vec<Atomic>,
    // This is private due to wanting to ensure we construct the ranges correctly via `as_simplified_range`
    ranges: BTreeMap<ContextVarNode, SolcRange>,
    atomic_ranges: BTreeMap<Atomic, SolcRange>,
    pub lmrs: Vec<LMR>,
    pub intermediate_ranges: BTreeMap<ContextVarNode, SolcRange>,
    pub intermediate_atomic_ranges: BTreeMap<Atomic, SolcRange>,
    pub sat: bool,
    pub start_idx: usize,
    pub successful_passes: usize,
}

#[derive(Clone, Debug)]
pub struct LMR {
    pub low: Elem<Concrete>,
    pub mid: Elem<Concrete>,
    pub high: Elem<Concrete>,
}

impl From<(Elem<Concrete>, Elem<Concrete>, Elem<Concrete>)> for LMR {
    fn from((low, mid, high): (Elem<Concrete>, Elem<Concrete>, Elem<Concrete>)) -> Self {
        Self { low, mid, high }
    }
}

pub enum HintOrRanges {
    Higher,
    Lower,
    Ranges(BTreeMap<ContextVarNode, SolcRange>),
}

impl BruteBinSearchSolver {
    pub fn maybe_new(
        deps: Vec<ContextVarNode>,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<Self>, GraphError> {
        let mut atomic_idxs = vec![];

        let mut ranges = BTreeMap::default();
        let mut atomic_ranges = BTreeMap::default();
        deps.iter().try_for_each(|dep| {
            let mut range = dep.range(analyzer)?.unwrap();
            if range.unsat(analyzer, arena) {
                panic!(
                    "initial range for {} not sat",
                    dep.display_name(analyzer).unwrap()
                );
            }
            let r: SolcRange = range.flattened_range(analyzer, arena)?.into_owned().into();
            atomic_idxs.extend(r.dependent_on(analyzer, arena));
            ranges.insert(*dep, r);
            Ok(())
        })?;

        // Sometimes a storage variable will be split due to a context fork. We recombine them here
        atomic_idxs.sort();
        atomic_idxs.dedup();
        // let atomics = atomic_idxs;
        let mut storage_atomics: BTreeMap<VarNode, Vec<ContextVarNode>> = BTreeMap::default();
        let mut calldata_atomics = vec![];
        atomic_idxs.into_iter().try_for_each(|atomic| {
            if atomic.is_storage(analyzer)? {
                // its a storage variable, get the parent var
                if atomic.is_dyn(analyzer)? {
                } else {
                    let entry = storage_atomics
                        .entry(atomic.maybe_storage_var(analyzer).unwrap())
                        .or_default();
                    entry.push(atomic);
                    entry.sort();
                    entry.dedup();
                }
            } else {
                calldata_atomics.push(atomic);
            }
            Ok(())
        })?;

        let mut atomics: Vec<Atomic> = vec![];
        storage_atomics
            .into_iter()
            .for_each(|(_k, same_atomics)| atomics.push(Atomic { idxs: same_atomics }));
        atomics.extend(
            calldata_atomics
                .into_iter()
                .map(|atomic| Atomic { idxs: vec![atomic] })
                .collect::<Vec<_>>(),
        );

        atomics.iter().try_for_each(|atomic| {
            let range = atomic.idxs[0].range(analyzer)?.unwrap();
            atomic_ranges.insert(atomic.clone(), range);
            Ok(())
        })?;
        if let Some((dep, unsat_range)) = ranges
            .iter()
            .find(|(_, range)| range.unsat(analyzer, arena))
        {
            panic!(
                "Initial ranges not sat for dep {}: {} {}",
                dep.display_name(analyzer).unwrap(),
                unsat_range.min,
                unsat_range.max
            );
        }

        if ranges.len() != deps.len() {
            panic!("HERE");
        }

        let mut s = Self {
            deps,
            solves: Default::default(),
            atomics,
            intermediate_ranges: ranges.clone(),
            ranges,
            intermediate_atomic_ranges: atomic_ranges.clone(),
            atomic_ranges,
            lmrs: vec![],
            sat: true,
            start_idx: 0,
            successful_passes: 0,
        };

        s.reset_lmrs(analyzer, arena);
        Ok(Some(s))
    }

    pub fn lmr(
        &self,
        atomic: &Atomic,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (Elem<Concrete>, Elem<Concrete>, Elem<Concrete>) {
        let range = &self.atomic_ranges[atomic];
        let mut min = range.evaled_range_min(analyzer, arena).unwrap();
        min.cache_minimize(analyzer, arena).unwrap();
        let mut max = range.evaled_range_max(analyzer, arena).unwrap();
        max.cache_maximize(analyzer, arena).unwrap();
        let mut mid = (min.clone() + max.clone()) / Elem::from(Concrete::from(U256::from(2)));
        mid.cache_maximize(analyzer, arena).unwrap();
        (min, mid, max)
    }

    pub fn reset_lmrs(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.lmrs = vec![];
        (0..self.atomic_ranges.len()).for_each(|i| {
            self.lmrs
                .push(self.lmr(&self.atomics[i], analyzer, arena).into());
        });
    }

    pub fn reset_lmr(
        &mut self,
        i: usize,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.lmrs[i] = self.lmr(&self.atomics[i], analyzer, arena).into();
    }

    pub fn raise_lmr(
        &mut self,
        i: usize,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        // move the low to low + mid / 2
        // reset the mid
        let mut curr_lmr = self.lmrs[i].clone();
        curr_lmr.low = (curr_lmr.low + curr_lmr.mid)
            / Elem::from(Concrete::from(U256::from(2)))
                .minimize(analyzer, arena)
                .unwrap();
        curr_lmr.mid = (curr_lmr.low.clone() + curr_lmr.high.clone())
            / Elem::from(Concrete::from(U256::from(2)))
                .minimize(analyzer, arena)
                .unwrap();

        let new_mid_conc = curr_lmr.mid.maximize(analyzer, arena).unwrap();
        let old_mid_conc = self.lmrs[i].mid.maximize(analyzer, arena).unwrap();

        if matches!(
            new_mid_conc.range_ord(&old_mid_conc, arena),
            Some(std::cmp::Ordering::Equal)
        ) {
            return false;
        }
        self.lmrs[i] = curr_lmr;
        true
    }

    pub fn lower_lmr(
        &mut self,
        i: usize,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        // move the high to high + mid / 2
        // reset the mid
        let mut curr_lmr = self.lmrs[i].clone();
        curr_lmr.high = (curr_lmr.mid.minimize(analyzer, arena).unwrap()
            + curr_lmr.high.minimize(analyzer, arena).unwrap())
            / Elem::from(Concrete::from(U256::from(2)))
                .minimize(analyzer, arena)
                .unwrap();
        curr_lmr.mid = (curr_lmr.low.minimize(analyzer, arena).unwrap()
            + curr_lmr.high.minimize(analyzer, arena).unwrap())
            / Elem::from(Concrete::from(U256::from(2)))
                .minimize(analyzer, arena)
                .unwrap();

        let new_high_conc = curr_lmr.high.minimize(analyzer, arena).unwrap();
        let old_high_conc = self.lmrs[i].high.minimize(analyzer, arena).unwrap();

        if matches!(
            new_high_conc.range_ord(&old_high_conc, arena),
            Some(std::cmp::Ordering::Equal)
        ) {
            return false;
        }
        self.lmrs[i] = curr_lmr;
        true
    }

    pub fn increase_start(&mut self) -> bool {
        self.start_idx += 1;
        self.start_idx < self.atomic_ranges.len()
    }
}

impl SolcSolver for BruteBinSearchSolver {
    fn simplify(
        &mut self,
        _analyzer: &impl AnalyzerBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) {
    }

    fn solve(
        &mut self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<AtomicSolveStatus, GraphError> {
        // pick a value for a variable. check if it satisfies all dependendies
        // if is sat, try to reduce using bin search? Not sure how that will
        // affect other dependencies If it doesnt,
        // raise or lower

        let atoms = self
            .ranges
            .iter()
            .filter_map(|(_dep, range)| {
                if let Some(atom) = range.min.atomize(analyzer, arena) {
                    Some(atom)
                } else {
                    range.max.atomize(analyzer, arena)
                }
            })
            .collect::<Vec<SolverAtom>>();

        let mut dl_solver = DLSolver::new(atoms, analyzer, arena);
        let mut atomic_solves: BTreeMap<_, _>;

        match dl_solver.solve_partial(analyzer, arena)? {
            SolveStatus::Unsat => {
                return Ok(AtomicSolveStatus::Unsat);
            }
            SolveStatus::Sat {
                const_solves,
                dl_solves,
            } => {
                atomic_solves = const_solves
                    .into_iter()
                    .filter_map(|(dep, solve)| {
                        Some((
                            self.atomics
                                .iter()
                                .find(|atomic| atomic.idxs.contains(&dep))?
                                .clone(),
                            solve
                                .maximize(analyzer, arena)
                                .unwrap()
                                .maybe_concrete()?
                                .val,
                        ))
                    })
                    .collect();
                atomic_solves.extend(
                    dl_solves
                        .into_iter()
                        .filter_map(|(dep, solve)| {
                            Some((
                                self.atomics
                                    .iter()
                                    .find(|atomic| atomic.idxs.contains(&dep))?
                                    .clone(),
                                solve
                                    .maximize(analyzer, arena)
                                    .unwrap()
                                    .maybe_concrete()?
                                    .val,
                            ))
                        })
                        .collect::<Vec<_>>(),
                );
            }
            SolveStatus::Indeterminate { const_solves } => {
                atomic_solves = const_solves
                    .into_iter()
                    .filter_map(|(dep, solve)| {
                        Some((
                            self.atomics
                                .iter()
                                .find(|atomic| atomic.idxs.contains(&dep))?
                                .clone(),
                            solve
                                .maximize(analyzer, arena)
                                .unwrap()
                                .maybe_concrete()?
                                .val,
                        ))
                    })
                    .collect()
            }
        }

        if atomic_solves.len() == self.atomics.len() {
            return Ok(AtomicSolveStatus::Sat(atomic_solves));
        } else {
            atomic_solves.iter().for_each(|(atomic, val)| {
                self.intermediate_ranges.iter_mut().for_each(|(_dep, r)| {
                    atomic.idxs.iter().for_each(|idx| {
                        r.replace_dep(idx.0.into(), Elem::from(val.clone()), analyzer, arena)
                    });
                });
            });

            atomic_solves.clone().into_iter().for_each(|(atomic, val)| {
                self.intermediate_atomic_ranges.insert(
                    atomic,
                    SolcRange::new(val.clone().into(), val.into(), vec![]),
                );
            });
        }

        let mut solved_for = atomic_solves
            .keys()
            .filter_map(|k| self.atomics.iter().position(|r| r == k))
            .collect();
        while self.recurse_check(self.start_idx, &mut solved_for, analyzer, arena)? {}
        if self.successful_passes == self.atomics.len() {
            let mapping = self
                .intermediate_atomic_ranges
                .iter()
                .filter_map(|(name, range)| {
                    if !range.is_const(analyzer, arena).ok()? {
                        None
                    } else {
                        Some((
                            name.clone(),
                            range
                                .evaled_range_min(analyzer, arena)
                                .unwrap()
                                .maybe_concrete()
                                .unwrap()
                                .val,
                        ))
                    }
                })
                .collect::<BTreeMap<Atomic, Concrete>>();
            if mapping.len() == self.intermediate_atomic_ranges.len() {
                let all_good = self.ranges.iter().all(|(_dep, range)| {
                    let mut new_range = range.clone();
                    self.intermediate_atomic_ranges
                        .iter()
                        .for_each(|(atomic, range)| {
                            atomic.idxs.iter().for_each(|idx| {
                                new_range.replace_dep(
                                    idx.0.into(),
                                    range.min.clone(),
                                    analyzer,
                                    arena,
                                );
                            });
                        });
                    new_range.cache_eval(analyzer, arena).unwrap();
                    new_range.sat(analyzer, arena)
                });
                if all_good {
                    Ok(AtomicSolveStatus::Sat(mapping))
                } else {
                    Ok(AtomicSolveStatus::Indeterminate)
                }
            } else {
                Ok(AtomicSolveStatus::Indeterminate)
            }
        } else {
            Ok(AtomicSolveStatus::Indeterminate)
        }
    }

    fn recurse_check(
        &mut self,
        i: usize,
        solved_atomics: &mut Vec<usize>,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        if i >= self.lmrs.len() {
            return Ok(false);
        }

        if solved_atomics.contains(&i) {
            self.increase_start();
            self.successful_passes += 1;
            return Ok(true);
        }

        let _atomic = &self.atomics[i];

        let lmr = self.lmrs[i].clone();
        match self.check(
            i,
            (lmr.low, lmr.mid, lmr.high),
            solved_atomics,
            analyzer,
            arena,
        )? {
            (true, Some(HintOrRanges::Ranges(new_ranges))) => {
                // sat, try solving next var with new intermediate ranges
                solved_atomics.push(i);
                self.intermediate_ranges = new_ranges;
                self.successful_passes += 1;
                self.increase_start();
                Ok(true)
            }
            (false, Some(HintOrRanges::Higher)) => {
                self.successful_passes = 0;
                *solved_atomics = vec![];
                // unsat, try raising
                if self.raise_lmr(i, analyzer, arena) {
                    self.recurse_check(i, solved_atomics, analyzer, arena)
                } else {
                    // we couldn't solve, try increasing global start
                    if self.increase_start() {
                        self.intermediate_ranges = self.ranges.clone();
                        self.recurse_check(self.start_idx, solved_atomics, analyzer, arena)
                    } else {
                        Ok(false)
                    }
                }
            }
            (false, Some(HintOrRanges::Lower)) => {
                // unsat, try lowering
                self.successful_passes = 0;
                *solved_atomics = vec![];
                if self.lower_lmr(i, analyzer, arena) {
                    self.recurse_check(i, solved_atomics, analyzer, arena)
                } else {
                    // we couldn't solve, try increasing global start
                    if self.increase_start() {
                        self.intermediate_ranges = self.ranges.clone();
                        self.recurse_check(self.start_idx, solved_atomics, analyzer, arena)
                    } else {
                        Ok(false)
                    }
                }
            }
            (false, None) => {
                // unsat, try lowering
                self.successful_passes = 0;
                *solved_atomics = vec![];
                if self.lower_lmr(i, analyzer, arena) {
                    self.recurse_check(i, solved_atomics, analyzer, arena)
                } else {
                    // we couldn't solve, try increasing global start
                    if self.increase_start() {
                        self.intermediate_ranges = self.ranges.clone();
                        self.recurse_check(self.start_idx, solved_atomics, analyzer, arena)
                    } else {
                        Ok(false)
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    fn check(
        &mut self,
        solved_for_idx: usize,
        (low, mid, high): (Elem<Concrete>, Elem<Concrete>, Elem<Concrete>),
        solved_atomics: &mut Vec<usize>,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(bool, Option<HintOrRanges>), GraphError> {
        let solved_dep = &self.atomics[solved_for_idx].clone();

        fn match_check(
            this: &mut BruteBinSearchSolver,
            solved_for_idx: usize,
            solved_dep: &Atomic,
            (low, mid, high): (Elem<Concrete>, Elem<Concrete>, Elem<Concrete>),
            low_done: bool,
            mut mid_done: bool,
            mut high_done: bool,
            solved_atomics: &mut Vec<usize>,
            analyzer: &mut impl GraphBackend,
            arena: &mut RangeArena<Elem<Concrete>>,
        ) -> Result<(bool, Option<HintOrRanges>), GraphError> {
            let res = if !low_done {
                check_for_lmr(
                    this,
                    solved_for_idx,
                    solved_dep,
                    low.clone(),
                    solved_atomics,
                    analyzer,
                    arena,
                )
            } else if !mid_done {
                check_for_lmr(
                    this,
                    solved_for_idx,
                    solved_dep,
                    mid.clone(),
                    solved_atomics,
                    analyzer,
                    arena,
                )
            } else {
                check_for_lmr(
                    this,
                    solved_for_idx,
                    solved_dep,
                    high.clone(),
                    solved_atomics,
                    analyzer,
                    arena,
                )
            };

            match res {
                Ok((true, ranges)) => Ok((true, ranges)),
                Ok((false, _)) => {
                    if high_done {
                        res
                    } else {
                        high_done = mid_done;
                        mid_done = true;
                        match_check(
                            this,
                            solved_for_idx,
                            solved_dep,
                            (low, mid, high),
                            true,
                            mid_done,
                            high_done,
                            solved_atomics,
                            analyzer,
                            arena,
                        )
                    }
                }
                Err(e) => Err(e),
            }
        }

        fn check_for_lmr(
            this: &mut BruteBinSearchSolver,
            solved_for_idx: usize,
            solved_dep: &Atomic,
            conc: Elem<Concrete>,
            solved_atomics: &mut Vec<usize>,
            analyzer: &mut impl GraphBackend,
            arena: &mut RangeArena<Elem<Concrete>>,
        ) -> Result<(bool, Option<HintOrRanges>), GraphError> {
            solved_atomics.push(solved_for_idx);
            let mut new_ranges = BTreeMap::default();
            this.intermediate_atomic_ranges.insert(
                solved_dep.clone(),
                SolcRange::new(conc.clone(), conc.clone(), vec![]),
            );
            let atoms = this
                .intermediate_ranges
                .iter()
                .filter_map(|(_, range)| {
                    if let Some(atom) = range
                        .min
                        .simplify_minimize(analyzer, arena)
                        .unwrap()
                        .atomize(analyzer, arena)
                    {
                        Some(atom)
                    } else {
                        range
                            .max
                            .simplify_maximize(analyzer, arena)
                            .unwrap()
                            .atomize(analyzer, arena)
                    }
                })
                .collect::<Vec<SolverAtom>>();

            let mut dl_solver = DLSolver::new(atoms, analyzer, arena);
            let mut atomic_solves: BTreeMap<_, _>;

            match dl_solver.solve_partial(analyzer, arena)? {
                SolveStatus::Unsat => {
                    return Ok((false, None));
                }
                SolveStatus::Sat {
                    const_solves,
                    dl_solves,
                } => {
                    atomic_solves = const_solves
                        .into_iter()
                        .filter_map(|(dep, solve)| {
                            Some((
                                this.atomics
                                    .iter()
                                    .find(|atomic| atomic.idxs.contains(&dep))?
                                    .clone(),
                                solve
                                    .maximize(analyzer, arena)
                                    .unwrap()
                                    .maybe_concrete()?
                                    .val,
                            ))
                        })
                        .collect();
                    atomic_solves.extend(
                        dl_solves
                            .into_iter()
                            .filter_map(|(dep, solve)| {
                                Some((
                                    this.atomics
                                        .iter()
                                        .find(|atomic| atomic.idxs.contains(&dep))?
                                        .clone(),
                                    solve
                                        .maximize(analyzer, arena)
                                        .unwrap()
                                        .maybe_concrete()?
                                        .val,
                                ))
                            })
                            .collect::<Vec<_>>(),
                    );
                }
                SolveStatus::Indeterminate { const_solves } => {
                    atomic_solves = const_solves
                        .into_iter()
                        .filter_map(|(dep, solve)| {
                            Some((
                                this.atomics
                                    .iter()
                                    .find(|atomic| atomic.idxs.contains(&dep))?
                                    .clone(),
                                solve
                                    .maximize(analyzer, arena)
                                    .unwrap()
                                    .maybe_concrete()?
                                    .val,
                            ))
                        })
                        .collect()
                }
            }

            atomic_solves.iter().for_each(|(atomic, val)| {
                this.intermediate_ranges.iter_mut().for_each(|(_dep, r)| {
                    atomic.idxs.iter().for_each(|idx| {
                        r.replace_dep(idx.0.into(), Elem::from(val.clone()), analyzer, arena)
                    });
                });
            });

            atomic_solves.clone().into_iter().for_each(|(atomic, val)| {
                this.intermediate_atomic_ranges.insert(
                    atomic,
                    SolcRange::new(val.clone().into(), val.into(), vec![]),
                );
            });

            for dep in this.deps.iter() {
                let range = this
                    .intermediate_ranges
                    .get(dep)
                    .expect("No range for dep?");
                if solved_dep.idxs.contains(dep) {
                    continue;
                }
                // check that the concrete value doesn't break any
                let mut new_range = range.clone();

                // check if the new range is dependent on the solved variable
                let is_dependent_on_solved = new_range
                    .dependent_on(analyzer, arena)
                    .iter()
                    .any(|dep| solved_dep.idxs.contains(dep));

                // dont run sat check on non-dependent range
                if !is_dependent_on_solved {
                    new_ranges.insert(*dep, new_range);
                    continue;
                }

                if new_range.unsat(analyzer, arena) {
                    return Ok((false, None));
                    // panic!("initial range unsat???")
                }

                this.atomics[solved_for_idx]
                    .idxs
                    .iter()
                    .for_each(|atomic_alias| {
                        new_range.replace_dep(atomic_alias.0.into(), conc.clone(), analyzer, arena);
                    });
                new_range.cache_eval(analyzer, arena)?;

                if new_range.unsat(analyzer, arena) {
                    // figure out *where* we need to increase or decrease
                    // work on the unreplace range for now

                    // compare new range to prev range to see if they moved down or up

                    let min_change = new_range
                        .evaled_range_min(analyzer, arena)?
                        .range_ord(&range.evaled_range_min(analyzer, arena)?, arena);
                    let max_change = new_range
                        .evaled_range_max(analyzer, arena)?
                        .range_ord(&range.evaled_range_max(analyzer, arena)?, arena);
                    match (min_change, max_change) {
                        (Some(std::cmp::Ordering::Less), Some(std::cmp::Ordering::Greater)) => {
                            // panic!("initial range must have been unsat to start");
                        }
                        (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less)) => {
                            // we shrank our range, dont give a hint
                            return Ok((false, None));
                        }
                        (Some(std::cmp::Ordering::Greater), _) => {
                            // both grew, try lowering
                            return Ok((false, Some(HintOrRanges::Lower)));
                        }

                        (Some(std::cmp::Ordering::Less), _) => {
                            // both grew, try lowering
                            return Ok((false, Some(HintOrRanges::Higher)));
                        }
                        _ => {
                            return Ok((false, None));
                        }
                    }
                } else {
                    new_ranges.insert(*dep, new_range);
                }
            }
            Ok((true, Some(HintOrRanges::Ranges(new_ranges))))
        }

        match_check(
            self,
            solved_for_idx,
            solved_dep,
            (low, mid, high),
            false,
            false,
            false,
            solved_atomics,
            analyzer,
            arena,
        )
    }
}
