use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::*,
    solvers::{AtomOrPart, Atomize, OpType, SolverAtom},
    GraphBackend, GraphError,
};

use ethers_core::types::{I256, U256};
use itertools::Itertools;
use petgraph::{
    graph::NodeIndex,
    stable_graph::StableGraph,
    visit::{EdgeRef, IntoNodeIdentifiers, NodeIndexable, VisitMap, Visitable},
    Directed,
};

use std::collections::BTreeMap;

pub type DLGraph = StableGraph<AtomOrPart, AtomOrPart, Directed, usize>;

#[derive(Debug, Clone, Default)]
pub struct DLSolver {
    constraints: Vec<SolverAtom>,
    normalized_constraints: BTreeMap<SolverAtom, Vec<Vec<SolverAtom>>>,
    root_node: NodeIndex<usize>,
    pub const_solves: SolveMap,
    pub cached_dl_solves: Option<SolveMap>,
    pub graph: DLGraph,
    pub graph_map: BTreeMap<AtomOrPart, NodeIndex<usize>>,
    pub var_to_atom_idx: BTreeMap<ContextVarNode, NodeIndex<usize>>,
}

impl PartialEq for DLSolver {
    fn eq(&self, other: &Self) -> bool {
        self.constraints() == other.constraints()
            && self.graph_map == other.graph_map
            && self.var_to_atom_idx == other.var_to_atom_idx
    }
}

impl Eq for DLSolver {}

pub enum SolveStatus {
    Unsat,
    Sat {
        const_solves: SolveMap,
        dl_solves: SolveMap,
    },
    Indeterminate {
        const_solves: SolveMap,
    },
}

pub type SolveMap = BTreeMap<ContextVarNode, Elem<Concrete>>;

pub struct DLSolveResult {
    pub status: SolveStatus,
    pub added_atoms: Vec<AtomOrPart>,
    pub added_deps: Vec<ContextVarNode>,
}

impl DLSolver {
    pub fn new(mut constraints: Vec<SolverAtom>) -> Self {
        constraints.iter_mut().for_each(|c| {
            c.update_max_ty();
        });
        let mut graph: DLGraph = Default::default();
        let root_node = graph.add_node(AtomOrPart::Part(Elem::Null));
        let mut s = Self {
            constraints,
            graph,
            root_node,
            ..Default::default()
        };
        s.add_constraints(vec![]);
        s
    }

    pub fn constraints(&self) -> &[SolverAtom] {
        &self.constraints
    }

    pub fn add_constraint(
        &mut self,
        mut constraint: SolverAtom,
        normalized_forms: Vec<Vec<SolverAtom>>,
    ) {
        if !self.constraints.contains(&constraint) {
            constraint.update_max_ty();
            self.constraints.push(constraint.clone());
            self.normalized_constraints
                .insert(constraint.clone(), normalized_forms);
            self.cached_dl_solves = None;
        }
    }

    pub fn add_constraints(
        &mut self,
        constraints: Vec<SolverAtom>,
    ) -> BTreeMap<SolverAtom, Vec<Vec<SolverAtom>>> {
        let mut dep_to_solve_ty: BTreeMap<ContextVarNode, Vec<SolverAtom>> = BTreeMap::default();
        self.constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on();
            deps.into_iter().for_each(|dep| {
                if let Some(entry) = dep_to_solve_ty.get_mut(&dep) {
                    if constraint.ty == OpType::Const {
                        *entry = vec![constraint.clone()];
                    } else if entry[0].ty != OpType::Const {
                        // Constant requirements always take precedent
                        entry.push(constraint.clone());
                    }
                } else {
                    dep_to_solve_ty.insert(dep, vec![constraint.clone()]);
                }
            });
        });

        let constraints: Vec<_> = constraints
            .iter()
            .filter(|c| !self.constraints.contains(c))
            .collect();

        constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on();
            deps.into_iter().for_each(|dep| {
                if let Some(entry) = dep_to_solve_ty.get_mut(&dep) {
                    if constraint.ty == OpType::Const {
                        *entry = vec![(*constraint).clone()];
                    } else if entry[0].ty != OpType::Const {
                        // Constant requirements always take precedent
                        entry.push((*constraint).clone());
                    }
                } else {
                    dep_to_solve_ty.insert(dep, vec![(*constraint).clone()]);
                }
            });
        });

        // filter out self equality
        let non_self_equality: Vec<_> = dep_to_solve_ty
            .iter()
            .filter_map(|(dep, atoms)| {
                if atoms.len() == 1 && atoms[0].op == RangeOp::Eq && atoms[0].lhs == atoms[0].rhs {
                    return None;
                }
                Some((*dep, atoms))
            })
            .collect();
        // solve constant deps
        let const_solves = non_self_equality
            .iter()
            .filter_map(|(dep, atoms)| {
                if atoms.len() == 1 && atoms[0].ty == OpType::Const {
                    if atoms[0].rhs.is_part() {
                        return Some((*dep, atoms[0].rhs.into_elem()));
                    } else {
                        return Some((*dep, atoms[0].lhs.into_elem()));
                    }
                }
                None
            })
            .collect::<BTreeMap<_, _>>();
        self.const_solves = const_solves.clone();

        // widdle down constraints based on if we constant solved them
        let still_unknown_constraints: Vec<_> = self
            .constraints
            .clone()
            .into_iter()
            .filter(|constraint| {
                let deps = constraint.dependent_on();
                !deps.iter().all(|dep| const_solves.contains_key(dep))
            })
            .collect();

        if still_unknown_constraints.is_empty() {
            return Default::default();
        }

        still_unknown_constraints
            .into_iter()
            .filter(|constraint| {
                let deps = constraint.dependent_on();
                deps.iter().all(|dep| {
                    dep_to_solve_ty
                        .get(dep)
                        .unwrap()
                        .iter()
                        .all(|constraint| constraint.ty == OpType::DL)
                })
            })
            .map(|constraint| (constraint.clone(), Self::dl_atom_normalize(constraint)))
            .collect::<BTreeMap<SolverAtom, Vec<Vec<SolverAtom>>>>()
    }

    pub fn dl_solvable_constraints(&self) -> Vec<Vec<Vec<SolverAtom>>> {
        self.normalized_constraints.values().cloned().collect()
    }

    pub fn solve_partial(
        &mut self,
        analyzer: &impl GraphBackend,
    ) -> Result<SolveStatus, GraphError> {
        let mut dep_to_solve_ty: BTreeMap<ContextVarNode, Vec<SolverAtom>> = BTreeMap::default();
        self.constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on();
            deps.into_iter().for_each(|dep| {
                if let Some(entry) = dep_to_solve_ty.get_mut(&dep) {
                    if constraint.ty == OpType::Const {
                        *entry = vec![constraint.clone()];
                    } else if entry[0].ty != OpType::Const {
                        // Constant requirements always take precedent
                        entry.push(constraint.clone());
                    }
                } else {
                    dep_to_solve_ty.insert(dep, vec![constraint.clone()]);
                }
            });
        });

        if let Some(_self_inequality) = dep_to_solve_ty.iter().find(|(_dep, atoms)| {
            atoms.iter().any(|atom| {
                atom.op == RangeOp::Neq
                    && atom.lhs == atom.rhs
                    && !atom.lhs.dependent_on().is_empty()
            })
        }) {
            return Ok(SolveStatus::Unsat);
        }

        // filter out self equality
        let non_self_equality: Vec<_> = dep_to_solve_ty
            .iter()
            .filter_map(|(dep, atoms)| {
                if atoms.len() == 1 && atoms[0].op == RangeOp::Eq && atoms[0].lhs == atoms[0].rhs {
                    return None;
                }
                Some((*dep, atoms))
            })
            .collect();
        // solve constant deps
        let const_solves = non_self_equality
            .iter()
            .filter_map(|(dep, atoms)| {
                if atoms.len() == 1 && atoms[0].ty == OpType::Const {
                    if atoms[0].rhs.is_part() {
                        return Some((*dep, atoms[0].rhs.into_elem()));
                    } else {
                        return Some((*dep, atoms[0].lhs.into_elem()));
                    }
                }
                None
            })
            .collect::<BTreeMap<_, _>>();

        // println!("const solves: {const_solves:#?}");

        // widdle down constraints based on if we constant solved them
        let still_unknown_constraints: Vec<_> = self
            .constraints
            .clone()
            .into_iter()
            .filter(|constraint| {
                let deps = constraint.dependent_on();
                !deps.iter().all(|dep| const_solves.contains_key(dep))
            })
            .collect();

        if still_unknown_constraints.is_empty() {
            // TODO: Check that the constraints still hold
            return Ok(SolveStatus::Sat {
                const_solves,
                dl_solves: Default::default(),
            });
        }

        let dl_solvable = self.dl_solvable_constraints();
        // constraints -> paths -> constraint

        let basic: Vec<SolverAtom> = dl_solvable
            .iter()
            .filter_map(|c| if c.len() == 1 { Some(c.clone()) } else { None })
            .flatten()
            .flatten()
            .collect();

        // check if basics are unsat, if so the extra constraints wont help that
        // so its truly unsat
        let basic_solve = self.dl_solve(basic.clone(), analyzer)?;
        if matches!(basic_solve.status, SolveStatus::Unsat) {
            return Ok(SolveStatus::Unsat);
        }

        let multi: Vec<_> = dl_solvable
            .iter()
            .filter_map(|c| if c.len() > 1 { Some(c.clone()) } else { None })
            .collect();

        if multi.is_empty() {
            // we had no branches, just use the basic solve
            return match basic_solve.status {
                SolveStatus::Unsat => Ok(SolveStatus::Unsat),
                SolveStatus::Sat { dl_solves, .. } => Ok(SolveStatus::Sat {
                    const_solves,
                    dl_solves,
                }),
                SolveStatus::Indeterminate { .. } => {
                    Ok(SolveStatus::Indeterminate { const_solves })
                }
            };
        } else if !basic.is_empty() {
            let mut cnt = 0;
            let mut unsat = 0;
            for permutation in multi.iter().multi_cartesian_product() {
                cnt += 1;
                // flatten out the permutation
                let mut flattened: Vec<SolverAtom> = permutation
                    .into_iter()
                    .flat_map(|constraint| constraint.clone())
                    .collect();
                // add the constant paths
                flattened.extend(basic.clone());
                let solve = self.dl_solve(flattened, analyzer)?;
                // remove the added constraints, keeping the basic graph in tact
                self.remove_added(&solve);
                // now that we checked that
                match solve.status {
                    SolveStatus::Sat { dl_solves, .. } => {
                        return Ok(SolveStatus::Sat {
                            const_solves,
                            dl_solves,
                        });
                    }
                    SolveStatus::Unsat => {
                        unsat += 1;
                        continue;
                    }
                    SolveStatus::Indeterminate { .. } => continue,
                }
            }

            if cnt == unsat {
                return Ok(SolveStatus::Unsat);
            }
        }

        Ok(SolveStatus::Indeterminate { const_solves })
    }

    pub fn remove_added(&mut self, result: &DLSolveResult) {
        result.added_atoms.iter().for_each(|c| {
            let idx = self.graph_map.remove(c).unwrap();
            self.graph.remove_node(idx);
        });
        result.added_deps.iter().for_each(|dep| {
            self.var_to_atom_idx.remove(dep);
        });
    }

    pub fn dl_solve(
        &mut self,
        normalized_constraints: Vec<SolverAtom>,
        analyzer: &impl GraphBackend,
    ) -> Result<DLSolveResult, GraphError> {
        let mut added_atoms = vec![];
        let mut added_deps = vec![];
        if normalized_constraints.is_empty() {
            return Ok(DLSolveResult {
                status: SolveStatus::Indeterminate {
                    const_solves: Default::default(),
                },
                added_atoms,
                added_deps,
            });
        }
        let zero_part = AtomOrPart::Part(Elem::from(Concrete::from(U256::zero())));
        let mut indeterminate = false;
        normalized_constraints.iter().for_each(|constraint| {
            let a = if let Some(idx) = self.graph_map.get(&constraint.lhs.clone()) {
                *idx
            } else {
                let idx = self.graph.add_node(*constraint.lhs.clone());
                self.graph_map.insert(*constraint.lhs.clone(), idx);
                added_atoms.push(*constraint.lhs.clone());
                idx
            };

            let rhs_atom = constraint.rhs.expect_atom();
            let rhs_lhs_deps = rhs_atom.lhs.dependent_on();
            let rhs_rhs_deps = rhs_atom.rhs.dependent_on();
            let ((dyn_elem, dep), const_elem) =
                match (!rhs_lhs_deps.is_empty(), !rhs_rhs_deps.is_empty()) {
                    (true, true) => {
                        // panic!("here: {} {} {}", constraint.lhs.into_elem(), constraint.op.to_string(), rhs_atom.into_expr_elem());
                        indeterminate = true;
                        return;
                    }
                    (true, false) => {
                        if matches!(rhs_atom.op, RangeOp::Sub(_)) {
                            let const_elem = (rhs_atom.rhs.into_elem()
                                * Elem::from(Concrete::from(I256::from(-1))))
                            .maximize(analyzer)
                            .unwrap();
                            (
                                (rhs_atom.lhs, Some(rhs_lhs_deps[0])),
                                Box::new(AtomOrPart::Part(const_elem)),
                            )
                        } else {
                            ((rhs_atom.lhs, Some(rhs_lhs_deps[0])), rhs_atom.rhs)
                        }
                    }
                    (false, true) => {
                        if matches!(rhs_atom.op, RangeOp::Sub(_)) {
                            let const_elem = (rhs_atom.lhs.into_elem()
                                * Elem::from(Concrete::from(I256::from(-1))))
                            .maximize(analyzer)
                            .unwrap();
                            (
                                (rhs_atom.rhs, Some(rhs_rhs_deps[0])),
                                Box::new(AtomOrPart::Part(const_elem)),
                            )
                        } else {
                            ((rhs_atom.rhs, Some(rhs_rhs_deps[0])), rhs_atom.lhs)
                        }
                    }
                    (false, false) => {
                        if *rhs_atom.rhs == zero_part {
                            ((rhs_atom.rhs, None), rhs_atom.lhs)
                        } else {
                            ((rhs_atom.lhs, None), rhs_atom.rhs)
                        }
                    }
                };

            let b = if let Some(idx) = self.graph_map.get(&dyn_elem) {
                *idx
            } else {
                let idx = self.graph.add_node(*dyn_elem.clone());
                added_atoms.push(*dyn_elem.clone());
                self.graph_map.insert(*dyn_elem, idx);
                if let Some(dep) = dep {
                    if self.var_to_atom_idx.get(&dep).is_none() {
                        added_deps.push(dep);
                        self.var_to_atom_idx.insert(dep, idx);
                    }
                }
                idx
            };

            self.graph.add_edge(a, b, *const_elem);
        });

        let root_node = self.root_node;
        added_atoms.iter().for_each(|c| {
            let idx = self.graph_map.get(c).unwrap();
            self.graph.add_edge(
                root_node,
                *idx,
                AtomOrPart::Part(Elem::from(Concrete::from(U256::zero()))),
            );
        });

        if find_negative_cycle(&self.graph, root_node, analyzer).is_some() {
            return Ok(DLSolveResult {
                status: SolveStatus::Unsat,
                added_atoms,
                added_deps,
            });
        }

        let (mut dists, _) = bellman_ford_initialize_relax(&self.graph, root_node, analyzer);

        dists = dists
            .into_iter()
            .map(|dist| {
                (dist * Elem::from(Concrete::from(I256::from(-1))))
                    .maximize(analyzer)
                    .unwrap()
            })
            .collect();

        let res = self
            .var_to_atom_idx
            .iter()
            .map(|(dep, idx)| (*dep, dists[idx.index()].clone()))
            .collect();

        if indeterminate {
            return Ok(DLSolveResult {
                status: SolveStatus::Indeterminate {
                    const_solves: Default::default(),
                },
                added_atoms,
                added_deps,
            });
        }

        Ok(DLSolveResult {
            status: SolveStatus::Sat {
                const_solves: Default::default(),
                dl_solves: res,
            },
            added_atoms,
            added_deps,
        })
    }

    /// Normalizes a DL atom into x <= y - k, where x and y are variables and k is a constant.
    /// Needed for running negative cycle check. Additionally, if we have an `OR`, we
    pub fn dl_atom_normalize(constraint: SolverAtom) -> Vec<Vec<SolverAtom>> {
        // println!("normalizing: {}", constraint.into_expr_elem());
        let zero_part = AtomOrPart::Part(Elem::from(Concrete::from(U256::zero())));
        let false_part = AtomOrPart::Part(Elem::from(Concrete::from(false)));
        let true_part = AtomOrPart::Part(Elem::from(Concrete::from(true)));

        match (
            *constraint.lhs == true_part || *constraint.lhs == false_part,
            *constraint.rhs == true_part || *constraint.rhs == false_part,
        ) {
            (true, true) => {
                if constraint.lhs == constraint.rhs {
                    // true == true || false == false, just disregard this atom
                    return vec![vec![]];
                } else {
                    panic!("During normalization of a DL atom, got true == false");
                }
            }
            (true, false) => {
                // lhs is just a boolean, drop it
                return Self::dl_atom_normalize(constraint.rhs.as_solver_atom());
            }
            (false, true) => {
                // rhs is just a boolean, drop it
                return Self::dl_atom_normalize(constraint.lhs.as_solver_atom());
            }
            _ => {}
        }
        match constraint.op {
            RangeOp::Eq => {
                // convert `x == y` into `x <= y - 0 || y <= x - 0`
                let mut res = Self::dl_atom_normalize(SolverAtom {
                    ty: OpType::DL,
                    lhs: constraint.lhs.clone(),
                    op: RangeOp::Lte,
                    rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.rhs.clone(),
                        op: RangeOp::Sub(true),
                        rhs: Box::new(zero_part.clone()),
                    })),
                });

                assert!(res.len() == 1);
                res[0].extend(
                    Self::dl_atom_normalize(SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.rhs,
                        op: RangeOp::Lte,
                        rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.lhs,
                            op: RangeOp::Sub(true),
                            rhs: Box::new(zero_part.clone()),
                        })),
                    })
                    .remove(0),
                );
                res
            }
            RangeOp::Neq => {
                // convert `x != y` into `x <= y - 1 || y <= x - 1`
                let mut res = Self::dl_atom_normalize(SolverAtom {
                    ty: OpType::DL,
                    lhs: constraint.lhs.clone(),
                    op: RangeOp::Lte,
                    rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.rhs.clone(),
                        op: RangeOp::Sub(true),
                        rhs: Box::new(AtomOrPart::Part(Elem::from(Concrete::from(U256::from(1))))),
                    })),
                });

                assert!(res.len() == 1);

                res[0].extend(
                    Self::dl_atom_normalize(SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.rhs,
                        op: RangeOp::Lte,
                        rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.lhs,
                            op: RangeOp::Sub(true),
                            rhs: Box::new(AtomOrPart::Part(Elem::from(Concrete::from(
                                U256::from(1),
                            )))),
                        })),
                    })
                    .remove(0),
                );
                res
            }
            RangeOp::Lt => {
                let lhs_symb = !constraint.lhs.dependent_on().is_empty();
                let rhs_symb = !constraint.rhs.dependent_on().is_empty();
                match (lhs_symb, rhs_symb) {
                    (true, true) => {
                        let new_lhs = AtomOrPart::Atom(
                            constraint
                                .lhs
                                .into_elem()
                                .wrapping_sub(constraint.rhs.into_elem())
                                .atomize()
                                .expect("unable to atomize?"),
                        );
                        Self::dl_atom_normalize(SolverAtom {
                            ty: OpType::DL,
                            lhs: Box::new(new_lhs),
                            op: RangeOp::Lte,
                            rhs: Box::new(AtomOrPart::Part(Elem::from(Concrete::from(
                                I256::from(-1),
                            )))),
                        })
                    }
                    (true, false) => {
                        let new_lhs = AtomOrPart::Atom(
                            constraint
                                .lhs
                                .into_elem()
                                .wrapping_sub(Elem::from(Concrete::from(U256::zero())))
                                .atomize()
                                .expect("unable to atomize?"),
                        );

                        Self::dl_atom_normalize(SolverAtom {
                            ty: OpType::DL,
                            lhs: Box::new(new_lhs),
                            op: RangeOp::Lte,
                            rhs: constraint.rhs,
                        })
                    }
                    (false, true) => {
                        let new_lhs = AtomOrPart::Atom(
                            Elem::from(Concrete::from(U256::zero()))
                                .wrapping_sub(constraint.rhs.into_elem())
                                .atomize()
                                .expect("unable to atomize?"),
                        );
                        Self::dl_atom_normalize(SolverAtom {
                            ty: OpType::DL,
                            lhs: Box::new(new_lhs),
                            op: RangeOp::Lte,
                            rhs: constraint.lhs,
                        })
                    }
                    _ => panic!("here"),
                }
            }
            RangeOp::Lte => {
                if constraint.lhs.is_atom() {
                    // some form of (x + k <= y)
                    let lhs_atom = constraint.lhs.expect_atom();
                    let atom_lhs_is_symb = !lhs_atom.lhs.dependent_on().is_empty();
                    let atom_rhs_is_symb = !lhs_atom.rhs.dependent_on().is_empty();

                    match lhs_atom.op {
                        RangeOp::Sub(_) => {
                            match (atom_lhs_is_symb, atom_rhs_is_symb) {
                                (false, _) => {
                                    // (k - x <= y)
                                    //   ==> (-k + x >= y)
                                    //   ==> (y <= x - k)
                                    Self::dl_atom_normalize(SolverAtom {
                                        ty: constraint.ty,
                                        lhs: constraint.rhs,
                                        op: constraint.op,
                                        rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                                            ty: constraint.ty,
                                            lhs: lhs_atom.rhs,
                                            op: RangeOp::Sub(true),
                                            rhs: Box::new(*lhs_atom.lhs),
                                        })),
                                    })
                                }
                                _ => {
                                    // (x - k <= y)
                                    //   ==> (x <= y + k)
                                    Self::dl_atom_normalize(SolverAtom {
                                        ty: constraint.ty,
                                        lhs: Box::new(*lhs_atom.lhs),
                                        op: constraint.op,
                                        rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                                            ty: constraint.ty,
                                            lhs: constraint.rhs,
                                            op: RangeOp::Add(true),
                                            rhs: Box::new(*lhs_atom.rhs),
                                        })),
                                    })
                                }
                            }
                        }
                        RangeOp::Add(_) => {
                            // (k + x <= y) || (x + k <= y)
                            //   ==> (x <= y - k)
                            Self::dl_atom_normalize(SolverAtom {
                                ty: constraint.ty,
                                lhs: Box::new(*lhs_atom.lhs),
                                op: constraint.op,
                                rhs: Box::new(AtomOrPart::Atom(SolverAtom {
                                    ty: constraint.ty,
                                    lhs: constraint.rhs,
                                    op: RangeOp::Sub(true),
                                    rhs: Box::new(*lhs_atom.rhs),
                                })),
                            })
                        }
                        RangeOp::And => {
                            let mut res = Self::dl_atom_normalize(SolverAtom {
                                ty: constraint.ty,
                                lhs: Box::new(*lhs_atom.lhs),
                                op: constraint.op,
                                rhs: constraint.rhs.clone(),
                            });

                            let mut rhs = Self::dl_atom_normalize(SolverAtom {
                                ty: constraint.ty,
                                lhs: Box::new(*lhs_atom.rhs),
                                op: constraint.op,
                                rhs: constraint.rhs.clone(),
                            });
                            match (res.len() > 1, rhs.len() > 1) {
                                (true, true) => {
                                    res.extend(rhs);
                                    res
                                }
                                (true, false) => {
                                    res.iter_mut().for_each(|path| path.extend(rhs[0].clone()));
                                    res
                                }
                                (false, true) => {
                                    rhs.iter_mut().for_each(|path| path.extend(res[0].clone()));
                                    rhs
                                }
                                (false, false) => {
                                    res[0].extend(rhs.remove(0));
                                    res
                                }
                            }
                        }
                        // RangeOp::Eq => {
                        // 	// (atom.lhs == atom.rhs) <= rhs
                        // 	// try just swapping
                        // 	// rhs >=
                        // 	let new_lhs_atom = SolverAtom {
                        // 		ty: constraint.ty,
                        // 		lhs: lhs_atom.lhs,
                        // 		op: RangeOp::Sub(true),
                        // 		rhs: lhs_atom.rhs
                        // 	};
                        // 	Self::dl_atom_normalize(SolverAtom {
                        // 		ty: constraint.ty,
                        // 		lhs: Box::new(AtomOrPart::Atom(new_lhs_atom)),
                        // 		op: constraint.op,
                        // 		rhs: constraint.rhs.clone(),
                        // 	})
                        // }
                        // RangeOp::Neq => {
                        // 	// (atom.lhs != atom.rhs) <= rhs
                        // 	// (atom.lhs - atom.rhs) <= rhs
                        // 	let new_lhs_atom = SolverAtom {
                        // 		ty: constraint.ty,
                        // 		lhs: lhs_atom.lhs,
                        // 		op: RangeOp::Sub(true),
                        // 		rhs: lhs_atom.rhs
                        // 	};
                        // 	Self::dl_atom_normalize(SolverAtom {
                        // 		ty: constraint.ty,
                        // 		lhs: Box::new(AtomOrPart::Atom(new_lhs_atom)),
                        // 		op: constraint.op,
                        // 		rhs: constraint.rhs.clone(),
                        // 	})
                        // }
                        other => panic!("other op: {}, {constraint:#?}", other.to_string()),
                    }
                } else if constraint.rhs.is_part() {
                    let new_rhs = AtomOrPart::Atom(SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.rhs,
                        op: RangeOp::Sub(true),
                        rhs: Box::new(AtomOrPart::Part(Elem::from(Concrete::from(U256::zero())))),
                    });

                    Self::dl_atom_normalize(SolverAtom {
                        ty: constraint.ty,
                        lhs: constraint.lhs,
                        op: constraint.op,
                        rhs: Box::new(new_rhs),
                    })
                } else {
                    vec![vec![constraint]]
                }
            }
            RangeOp::Gte => Self::dl_atom_normalize(SolverAtom {
                ty: OpType::DL,
                lhs: constraint.rhs,
                op: RangeOp::Lte,
                rhs: constraint.lhs,
            }),
            RangeOp::Gt => Self::dl_atom_normalize(SolverAtom {
                ty: OpType::DL,
                lhs: constraint.rhs,
                op: RangeOp::Lt,
                rhs: constraint.lhs,
            }),
            RangeOp::Or => {
                let mut res = Self::dl_atom_normalize(constraint.lhs.as_solver_atom());
                res.extend(Self::dl_atom_normalize(constraint.rhs.as_solver_atom()));
                res
            }
            _other => {
                // println!("other: {}, {}", other.to_string(), constraint.into_expr_elem());
                Self::dl_atom_normalize(constraint)
            }
        }
    }
}

pub fn find_negative_cycle(
    g: &DLGraph,
    source: NodeIndex<usize>,
    analyzer: &impl GraphBackend,
) -> Option<Vec<NodeIndex<usize>>> {
    let ix = |i| g.to_index(i);
    let mut path = Vec::<NodeIndex<usize>>::new();

    // Step 1: initialize and relax
    let (distance, predecessor) = bellman_ford_initialize_relax(g, source, analyzer);

    // Step 2: Check for negative weight cycle
    'outer: for i in g.node_identifiers() {
        for edge in g.edges(i) {
            let j = edge.target();
            let w = edge.weight();
            let dist = (distance[ix(i)].clone() + w.into_elem())
                .maximize(analyzer)
                .unwrap();
            let lt = matches!(
                dist.range_ord(&distance[ix(j)]),
                Some(std::cmp::Ordering::Less)
            );
            if lt {
                // Step 3: negative cycle found
                let start = j;
                let mut node = start;
                let mut visited = g.visit_map();
                // Go backward in the predecessor chain
                loop {
                    let ancestor = match predecessor[ix(node)] {
                        Some(predecessor_node) => predecessor_node,
                        None => node, // no predecessor, self cycle
                    };
                    // We have only 2 ways to find the cycle and break the loop:
                    // 1. start is reached
                    if ancestor == start {
                        path.push(ancestor);
                        break;
                    }
                    // 2. some node was reached twice
                    else if visited.is_visited(&ancestor) {
                        // Drop any node in path that is before the first ancestor
                        let pos = path
                            .iter()
                            .position(|&p| p == ancestor)
                            .expect("we should always have a position");
                        path = path[pos..path.len()].to_vec();

                        break;
                    }

                    // None of the above, some middle path node
                    path.push(ancestor);
                    visited.visit(ancestor);
                    node = ancestor;
                }
                // We are done here
                break 'outer;
            }
        }
    }
    if !path.is_empty() {
        // Users will probably need to follow the path of the negative cycle
        // so it should be in the reverse order than it was found by the algorithm.
        path.reverse();
        Some(path)
    } else {
        None
    }
}

// Perform Step 1 and Step 2 of the Bellman-Ford algorithm.
#[inline(always)]
fn bellman_ford_initialize_relax(
    g: &DLGraph,
    source: NodeIndex<usize>,
    analyzer: &impl GraphBackend,
) -> (Vec<Elem<Concrete>>, Vec<Option<NodeIndex<usize>>>) {
    // Step 1: initialize graph
    let mut predecessor = vec![None; g.node_bound()];
    let mut distance = vec![Elem::from(Concrete::from(U256::MAX)); g.node_bound()];
    let ix = |i| g.to_index(i);
    distance[ix(source)] = Elem::from(Concrete::from(U256::zero()));

    // Step 2: relax edges repeatedly
    for _ in 1..g.node_count() {
        let mut did_update = false;
        for i in g.node_identifiers() {
            for edge in g.edges(i) {
                let j = edge.target();
                let w = edge.weight();
                let dist = (distance[ix(i)].clone() + w.into_elem())
                    .maximize(analyzer)
                    .unwrap();
                let lt = matches!(
                    dist.range_ord(&distance[ix(j)]),
                    Some(std::cmp::Ordering::Less)
                );
                if lt {
                    distance[ix(j)] = dist;
                    predecessor[ix(j)] = Some(i);
                    did_update = true;
                }
            }
        }
        if !did_update {
            break;
        }
    }
    (distance, predecessor)
}