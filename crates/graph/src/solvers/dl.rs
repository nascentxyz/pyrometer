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

use std::{collections::BTreeMap, rc::Rc};

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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct DLSolveResult {
    pub status: SolveStatus,
    pub added_atoms: Vec<AtomOrPart>,
    pub added_deps: Vec<ContextVarNode>,
}

impl DLSolver {
    pub fn new(mut constraints: Vec<SolverAtom>, analyzer: &mut impl GraphBackend) -> Self {
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
        s.add_constraints(vec![], analyzer);
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
        // println!("adding constraint");
        if !self.constraints.contains(&constraint) {
            // println!("didnt contain");
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
        analyzer: &mut impl GraphBackend,
    ) -> BTreeMap<SolverAtom, Vec<Vec<SolverAtom>>> {
        // println!("adding constriants: {constraints:#?}");
        let mut dep_to_solve_ty: BTreeMap<ContextVarNode, Vec<SolverAtom>> = BTreeMap::default();
        self.constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on(analyzer);
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

        // println!("dep_to_solve_ty: {dep_to_solve_ty:#?}");

        let constraints: Vec<_> = constraints
            .iter()
            .filter(|c| !self.constraints.contains(c))
            .collect();

        // println!("unique constraints: {constraints:#?}");

        constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on(analyzer);
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

        // println!("dep_to_solve_ty2: {dep_to_solve_ty:#?}");

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

        // println!("non_self_equality: {non_self_equality:#?}");
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
        // println!("const_solves: {const_solves:#?}");
        self.const_solves = const_solves.clone();

        // widdle down constraints based on if we constant solved them
        let still_unknown_constraints: Vec<_> = constraints
            .into_iter()
            .filter(|constraint| {
                let deps = constraint.dependent_on(analyzer);
                !deps.iter().all(|dep| const_solves.contains_key(dep))
            })
            .cloned()
            .collect();

        // println!("still_unknown_constraints: {still_unknown_constraints:#?}");

        if still_unknown_constraints.is_empty() {
            return Default::default();
        }

        let res = still_unknown_constraints
            .into_iter()
            .filter(|constraint| {
                let deps = constraint.dependent_on(analyzer);
                deps.iter().all(|dep| {
                    dep_to_solve_ty
                        .get(dep)
                        .unwrap()
                        .iter()
                        .all(|constraint| constraint.ty == OpType::DL)
                })
            })
            .collect::<Vec<_>>()
            .iter()
            .map(|constraint| {
                (
                    constraint.clone(),
                    Self::dl_atom_normalize(constraint.clone().clone(), analyzer),
                )
            })
            .collect::<BTreeMap<SolverAtom, Vec<Vec<SolverAtom>>>>();
        // println!("normalized map: {res:#?}");
        res
    }

    pub fn dl_solvable_constraints(&self) -> Vec<Vec<Vec<SolverAtom>>> {
        self.normalized_constraints.values().cloned().collect()
    }

    pub fn solve_partial(
        &mut self,
        analyzer: &impl GraphBackend,
    ) -> Result<SolveStatus, GraphError> {
        // println!("constraints {:#?}", self.constraints);
        let mut dep_to_solve_ty: BTreeMap<ContextVarNode, Vec<SolverAtom>> = BTreeMap::default();
        self.constraints.iter().for_each(|constraint| {
            let deps = constraint.dependent_on(analyzer);
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

        // println!("dep to solve: {dep_to_solve_ty:#?}");

        if let Some(_self_inequality) = dep_to_solve_ty.iter().find(|(_dep, atoms)| {
            atoms.iter().any(|atom| {
                atom.op == RangeOp::Neq
                    && atom.lhs == atom.rhs
                    && !atom.lhs.dependent_on(analyzer).is_empty()
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

        // println!("non_self_equality: {non_self_equality:#?}");
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
                let deps = constraint.dependent_on(analyzer);
                !deps.iter().all(|dep| const_solves.contains_key(dep))
            })
            .collect();

        // println!("still unknown: {still_unknown_constraints:#?}");

        if still_unknown_constraints.is_empty() {
            // TODO: Check that the constraints still hold
            return Ok(SolveStatus::Sat {
                const_solves,
                dl_solves: Default::default(),
            });
        }

        let dl_solvable = self.dl_solvable_constraints();
        // println!("dl solvable: {dl_solvable:#?}");
        // constraints -> paths -> constraint

        let basic: Vec<SolverAtom> = dl_solvable
            .iter()
            .filter_map(|c| if c.len() == 1 { Some(c.clone()) } else { None })
            .flatten()
            .flatten()
            .collect();

        // check if basics are unsat, if so the extra constraints wont help that
        // so its truly unsat
        // println!("basic: {basic:#?}");
        let basic_solve = self.dl_solve(basic.clone(), analyzer)?;
        if matches!(basic_solve.status, SolveStatus::Unsat) {
            return Ok(SolveStatus::Unsat);
        }

        // println!("basic solve: {basic_solve:?}");

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
            let a = if let Some(idx) = self.graph_map.get(&constraint.lhs) {
                *idx
            } else {
                let idx = self.graph.add_node((*constraint.lhs).clone());
                self.graph_map.insert((*constraint.lhs).clone(), idx);
                added_atoms.push((*constraint.lhs).clone());
                idx
            };

            let rhs_atom = constraint.rhs.expect_atom();
            let rhs_lhs_deps = rhs_atom.lhs.dependent_on(analyzer);
            let rhs_rhs_deps = rhs_atom.rhs.dependent_on(analyzer);
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
                                Rc::new(AtomOrPart::Part(const_elem)),
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
                                Rc::new(AtomOrPart::Part(const_elem)),
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
                let idx = self.graph.add_node((*dyn_elem).clone());
                added_atoms.push((*dyn_elem).clone());
                self.graph_map.insert((*dyn_elem).clone(), idx);
                if let Some(dep) = dep {
                    if self.var_to_atom_idx.get(&dep).is_none() {
                        added_deps.push(dep);
                        self.var_to_atom_idx.insert(dep, idx);
                    }
                }
                idx
            };

            self.graph.add_edge(a, b, (*const_elem).clone());
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
    pub fn dl_atom_normalize(
        constraint: SolverAtom,
        analyzer: &mut impl GraphBackend,
    ) -> Vec<Vec<SolverAtom>> {
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
                return Self::dl_atom_normalize(constraint.rhs.as_solver_atom(), analyzer);
            }
            (false, true) => {
                // rhs is just a boolean, drop it
                return Self::dl_atom_normalize(constraint.lhs.as_solver_atom(), analyzer);
            }
            _ => {}
        }

        // x <==> y
        // x + x + y => AtomOrPart::Atom(Atom { lhs x, op: +, rhs: AtomOrPart::Atom(Atom { lhs: x, op: +, rhs: y})})
        let lhs_symbs = constraint.lhs.dependent_on(analyzer);
        let rhs_symbs = constraint.rhs.dependent_on(analyzer);
        let constraint = match (!lhs_symbs.is_empty(), !rhs_symbs.is_empty()) {
            (true, true) => {
                // TODO: in theory could have x <op> x + y
                // which should simplify to 0 <op> y
                constraint
            }
            (true, false) => {
                // check for two vars on lhs
                if lhs_symbs.len() > 1 {
                    // two or more
                    let lhs = constraint.lhs.expect_atom();
                    match lhs.op {
                        RangeOp::Sub(_) => {
                            // x - y <op> z ==> x <op> z + y
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: lhs.lhs,
                                op: constraint.op,
                                rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                    ty: OpType::DL,
                                    lhs: constraint.rhs,
                                    op: RangeOp::Add(true),
                                    rhs: lhs.rhs,
                                })),
                            }
                        }
                        RangeOp::Add(_) => {
                            // x + y <op> z ==> x <op> z - y
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: lhs.lhs,
                                op: constraint.op,
                                rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                    ty: OpType::DL,
                                    lhs: constraint.rhs,
                                    op: RangeOp::Sub(true),
                                    rhs: lhs.rhs,
                                })),
                            }
                        }
                        _ => constraint
                    }
                } else {
                    // good
                    constraint
                }
            }
            (false, true) => {
                // check for two vars on lhs
                if rhs_symbs.len() > 1 {
                    // two or more
                    let rhs = constraint.rhs.expect_atom();
                    match rhs.op {
                        RangeOp::Sub(_) => {
                            // z <op> x - y ==> z + y <op> x
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                    ty: OpType::DL,
                                    lhs: constraint.lhs,
                                    op: RangeOp::Add(true),
                                    rhs: rhs.rhs                                       
                                })),
                                op: constraint.op,
                                rhs: rhs.lhs,
                            }
                        }
                        RangeOp::Add(_) => {
                            // z <op> x + y ==> z - y <op> x
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                    ty: OpType::DL,
                                    lhs: constraint.lhs,
                                    op: RangeOp::Sub(true),
                                    rhs: rhs.rhs                                       
                                })),
                                op: constraint.op,
                                rhs: rhs.lhs,
                            }
                        }
                        _ => constraint
                    }
                } else {
                    // good
                    constraint
                }
            }
            _ => constraint
        };


        println!("normalizing: {}", constraint.into_expr_elem());
        match constraint.op {
            RangeOp::Eq => {
                // convert `x == y` into `x <= y - 0 || y <= x - 0`
                let mut res = Self::dl_atom_normalize(
                    SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.lhs.clone(),
                        op: RangeOp::Lte,
                        rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.rhs.clone(),
                            op: RangeOp::Sub(true),
                            rhs: Rc::new(zero_part.clone()),
                        })),
                    },
                    analyzer,
                );

                assert!(res.len() == 1);
                res[0].extend(
                    Self::dl_atom_normalize(
                        SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.rhs,
                            op: RangeOp::Lte,
                            rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                ty: OpType::DL,
                                lhs: constraint.lhs,
                                op: RangeOp::Sub(true),
                                rhs: Rc::new(zero_part.clone()),
                            })),
                        },
                        analyzer,
                    )
                    .remove(0),
                );
                res
            }
            RangeOp::Neq => {
                // convert `x != y` into `x <= y - 1 || y <= x - 1`
                let mut res = Self::dl_atom_normalize(
                    SolverAtom {
                        ty: OpType::DL,
                        lhs: constraint.lhs.clone(),
                        op: RangeOp::Lte,
                        rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.rhs.clone(),
                            op: RangeOp::Sub(true),
                            rhs: Rc::new(AtomOrPart::Part(Elem::from(Concrete::from(U256::from(
                                1,
                            ))))),
                        })),
                    },
                    analyzer,
                );

                assert!(res.len() == 1);

                res[0].extend(
                    Self::dl_atom_normalize(
                        SolverAtom {
                            ty: OpType::DL,
                            lhs: constraint.rhs,
                            op: RangeOp::Lte,
                            rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                ty: OpType::DL,
                                lhs: constraint.lhs,
                                op: RangeOp::Sub(true),
                                rhs: Rc::new(AtomOrPart::Part(Elem::from(Concrete::from(
                                    U256::from(1),
                                )))),
                            })),
                        },
                        analyzer,
                    )
                    .remove(0),
                );
                res
            }
            RangeOp::Lt => {
                let lhs_symb = !constraint.lhs.dependent_on(analyzer).is_empty();
                let rhs_symb = !constraint.rhs.dependent_on(analyzer).is_empty();
                match (lhs_symb, rhs_symb) {
                    (true, true) => {
                        // x < y
                        // ==> x - y <= -1
                        let new_lhs = AtomOrPart::Atom(
                            constraint
                                .lhs
                                .into_elem()
                                .wrapping_sub(constraint.rhs.into_elem())
                                .atomize(analyzer)
                                .expect("unable to atomize?"),
                        );
                        Self::dl_atom_normalize(
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: Rc::new(new_lhs),
                                op: RangeOp::Lte,
                                rhs: Rc::new(AtomOrPart::Part(Elem::from(Concrete::from(
                                    I256::from(-1),
                                )))),
                            },
                            analyzer,
                        )
                    }
                    (true, false) => {
                        // x < k
                        // ==> x - 0 <= k
                        let new_lhs = AtomOrPart::Atom(
                            constraint
                                .lhs
                                .into_elem()
                                .wrapping_sub(Elem::from(Concrete::from(U256::zero())))
                                .atomize(analyzer)
                                .expect("unable to atomize?"),
                        );

                        Self::dl_atom_normalize(
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: Rc::new(new_lhs),
                                op: RangeOp::Lte,
                                rhs: constraint.rhs,
                            },
                            analyzer,
                        )
                    }
                    (false, true) => {
                        // k < x ==> k < (x - y)
                        // k < x
                        // ==>  0 - x <= k
                        let new_lhs = AtomOrPart::Atom(
                            Elem::from(Concrete::from(U256::zero()))
                                .wrapping_sub(constraint.rhs.into_elem())
                                .atomize(analyzer)
                                .expect("unable to atomize?"),
                        );
                        Self::dl_atom_normalize(
                            SolverAtom {
                                ty: OpType::DL,
                                lhs: Rc::new(new_lhs),
                                op: RangeOp::Lte,
                                rhs: constraint.lhs,
                            },
                            analyzer,
                        )
                            // }
                        // }
                    }
                    _ => panic!("here"),
                }
            }
            RangeOp::Lte => {
                if constraint.lhs.is_atom() {
                    // some form of (x + k <= y)
                    let lhs_atom = constraint.lhs.expect_atom();
                    let atom_lhs_is_symb = !lhs_atom.lhs.dependent_on(analyzer).is_empty();
                    let atom_rhs_is_symb = !lhs_atom.rhs.dependent_on(analyzer).is_empty();

                    match lhs_atom.op {
                        RangeOp::Sub(_) => {
                            match (atom_lhs_is_symb, atom_rhs_is_symb) {
                                (false, _) => {
                                    // (k - x <= y)
                                    //   ==> (-k + x >= y)
                                    //   ==> (y <= x - k)
                                    Self::dl_atom_normalize(
                                        SolverAtom {
                                            ty: constraint.ty,
                                            lhs: constraint.rhs,
                                            op: constraint.op,
                                            rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                                ty: constraint.ty,
                                                lhs: lhs_atom.rhs,
                                                op: RangeOp::Sub(true),
                                                rhs: lhs_atom.lhs,
                                            })),
                                        },
                                        analyzer,
                                    )
                                }
                                _ => {
                                    // (x - k <= y)
                                    //   ==> (x <= y + k)
                                    Self::dl_atom_normalize(
                                        SolverAtom {
                                            ty: constraint.ty,
                                            lhs: lhs_atom.lhs,
                                            op: constraint.op,
                                            rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                                ty: constraint.ty,
                                                lhs: constraint.rhs,
                                                op: RangeOp::Add(true),
                                                rhs: lhs_atom.rhs,
                                            })),
                                        },
                                        analyzer,
                                    )
                                }
                            }
                        }
                        RangeOp::Add(_) => {
                            if lhs_atom.lhs == zero_part.clone().into() {
                                Self::dl_atom_normalize(
                                    SolverAtom {
                                        ty: constraint.ty,
                                        lhs: lhs_atom.rhs,
                                        op: constraint.op,
                                        rhs: constraint.rhs,
                                    },
                                    analyzer,
                                )
                            } else if lhs_atom.rhs == zero_part.into() {
                                Self::dl_atom_normalize(
                                    SolverAtom {
                                        ty: constraint.ty,
                                        lhs: lhs_atom.lhs,
                                        op: constraint.op,
                                        rhs: constraint.rhs,
                                    },
                                    analyzer,
                                )
                            } else {
                                // (k + x <= y) || (x + k <= y)
                                //   ==> (x <= y - k)
                                Self::dl_atom_normalize(
                                    SolverAtom {
                                        ty: constraint.ty,
                                        lhs: lhs_atom.lhs,
                                        op: constraint.op,
                                        rhs: Rc::new(AtomOrPart::Atom(SolverAtom {
                                            ty: constraint.ty,
                                            lhs: constraint.rhs,
                                            op: RangeOp::Sub(true),
                                            rhs: lhs_atom.rhs,
                                        })),
                                    },
                                    analyzer,
                                )
                            }
                        }
                        RangeOp::And => {
                            let mut res = Self::dl_atom_normalize(
                                SolverAtom {
                                    ty: constraint.ty,
                                    lhs: lhs_atom.lhs,
                                    op: constraint.op,
                                    rhs: constraint.rhs.clone(),
                                },
                                analyzer,
                            );

                            let mut rhs = Self::dl_atom_normalize(
                                SolverAtom {
                                    ty: constraint.ty,
                                    lhs: lhs_atom.rhs,
                                    op: constraint.op,
                                    rhs: constraint.rhs.clone(),
                                },
                                analyzer,
                            );
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
                        rhs: Rc::new(AtomOrPart::Part(Elem::from(Concrete::from(U256::zero())))),
                    });

                    Self::dl_atom_normalize(
                        SolverAtom {
                            ty: constraint.ty,
                            lhs: constraint.lhs,
                            op: constraint.op,
                            rhs: Rc::new(new_rhs),
                        },
                        analyzer,
                    )
                } else {
                    vec![vec![constraint]]
                }
            }
            RangeOp::Gte => Self::dl_atom_normalize(
                SolverAtom {
                    ty: OpType::DL,
                    lhs: constraint.rhs,
                    op: RangeOp::Lte,
                    rhs: constraint.lhs,
                },
                analyzer,
            ),
            RangeOp::Gt => Self::dl_atom_normalize(
                SolverAtom {
                    ty: OpType::DL,
                    lhs: constraint.rhs,
                    op: RangeOp::Lt,
                    rhs: constraint.lhs,
                },
                analyzer,
            ),
            RangeOp::Or => {
                let mut res = Self::dl_atom_normalize(constraint.lhs.as_solver_atom(), analyzer);
                res.extend(Self::dl_atom_normalize(
                    constraint.rhs.as_solver_atom(),
                    analyzer,
                ));
                res
            }
            _other => {
                // println!("other: {}, {}", other.to_string(), constraint.into_expr_elem());
                Self::dl_atom_normalize(constraint, analyzer)
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
                dist.range_ord(&distance[ix(j)], analyzer),
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
                    dist.range_ord(&distance[ix(j)], analyzer),
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
