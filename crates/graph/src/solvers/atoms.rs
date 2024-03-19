use crate::elem::{collapse, MaybeCollapsed};
use crate::range::exec_traits::ExecOp;
use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{
        elem::{Elem, RangeElem, RangeExpr, RangeOp, Reference},
        range_string::{RangeElemString, ToRangeString},
    },
    GraphBackend,
};

use ethers_core::types::U256;
use std::{collections::BTreeMap, rc::Rc};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum AtomOrPart {
    Part(Elem<Concrete>),
    Atom(SolverAtom),
}

impl AtomOrPart {
    pub fn into_elem(&self) -> Elem<Concrete> {
        match self {
            AtomOrPart::Part(part) => part.clone(),
            AtomOrPart::Atom(atom) => atom.into_expr_elem(),
        }
    }

    pub fn as_solver_atom(&self) -> SolverAtom {
        match self {
            AtomOrPart::Part(_) => SolverAtom {
                ty: OpType::DL,
                lhs: Rc::new(self.clone()),
                op: RangeOp::Sub(false),
                rhs: Rc::new(AtomOrPart::Part(Elem::from(Concrete::from(U256::zero())))),
            },
            AtomOrPart::Atom(atom) => atom.clone(),
        }
    }

    pub fn replace_deps(
        &self,
        solves: &BTreeMap<ContextVarNode, Elem<Concrete>>,
        analyzer: &mut impl GraphBackend,
    ) -> Self {
        match self {
            AtomOrPart::Part(part) => {
                let mut new_part = part.clone();
                solves.iter().for_each(|(dep, replacement)| {
                    new_part.replace_dep(dep.0.into(), replacement.clone(), analyzer)
                });
                AtomOrPart::Part(new_part)
            }
            AtomOrPart::Atom(atom) => AtomOrPart::Atom(atom.replace_deps(solves, analyzer)),
        }
    }

    pub fn maybe_max_ty(&self) -> Option<OpType> {
        match self {
            AtomOrPart::Part(_part) => None,
            AtomOrPart::Atom(atom) => Some(atom.max_ty()),
        }
    }

    pub fn is_part(&self) -> bool {
        matches!(self, AtomOrPart::Part(_))
    }

    pub fn is_atom(&self) -> bool {
        matches!(self, AtomOrPart::Atom(_))
    }

    pub fn expect_atom(&self) -> SolverAtom {
        if let AtomOrPart::Atom(atom) = self {
            atom.clone()
        } else {
            panic!("Expected atom, was part: {self:?}")
        }
    }

    pub fn expect_part(&self) -> Elem<Concrete> {
        if let AtomOrPart::Part(part) = self {
            part.clone()
        } else {
            panic!("Expected part, was atom: {self:?}")
        }
    }

    pub fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        match self {
            AtomOrPart::Part(e) => e.dependent_on(analyzer),
            AtomOrPart::Atom(a) => a.dependent_on(analyzer),
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum OpType {
    Const,
    DL,
    Linear,
    Other,
}

impl OpType {
    pub fn new(op: RangeOp) -> Self {
        if LIA_OPS.contains(&op) {
            OpType::Linear
        } else if DL_OPS.contains(&op) {
            OpType::DL
        } else if CONST_OPS.contains(&op) {
            OpType::Const
        } else {
            OpType::Other
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SolverAtom {
    pub ty: OpType,
    pub lhs: Rc<AtomOrPart>,
    pub op: RangeOp,
    pub rhs: Rc<AtomOrPart>,
}

impl ToRangeString for SolverAtom {
    fn def_string(&self, analyzer: &impl GraphBackend) -> RangeElemString {
        self.into_expr_elem().def_string(analyzer)
    }
    fn to_range_string(&self, maximize: bool, analyzer: &impl GraphBackend) -> RangeElemString {
        self.into_expr_elem().to_range_string(maximize, analyzer)
    }
}

impl SolverAtom {
    pub fn replace_deps(
        &self,
        solves: &BTreeMap<ContextVarNode, Elem<Concrete>>,
        analyzer: &mut impl GraphBackend,
    ) -> Self {
        SolverAtom {
            ty: self.ty,
            lhs: Rc::new(self.lhs.clone().replace_deps(solves, analyzer)),
            op: self.op,
            rhs: Rc::new(self.rhs.clone().replace_deps(solves, analyzer)),
        }
    }

    pub fn max_ty(&self) -> OpType {
        let mut max = OpType::new(self.op);
        if let Some(lhs_max_ty) = self.lhs.maybe_max_ty() {
            if lhs_max_ty > max {
                max = lhs_max_ty;
            }
        }
        if let Some(rhs_max_ty) = self.rhs.maybe_max_ty() {
            if rhs_max_ty > max {
                max = rhs_max_ty;
            }
        }
        max
    }

    pub fn update_max_ty(&mut self) {
        self.ty = self.max_ty();
    }

    pub fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on(analyzer);
        deps.extend(self.rhs.dependent_on(analyzer));
        deps
    }

    pub fn into_expr_elem(&self) -> Elem<Concrete> {
        Elem::Expr(RangeExpr::new(
            self.lhs.into_elem(),
            self.op,
            self.rhs.into_elem(),
        ))
    }

    pub fn add_rhs(&self, op: RangeOp, rhs: AtomOrPart) -> Self {
        let new_ty = OpType::new(op);
        if self.ty >= new_ty {
            // keep ty
            Self {
                ty: self.ty,
                lhs: Rc::new(AtomOrPart::Atom(self.clone())),
                op,
                rhs: Rc::new(rhs),
            }
        } else {
            Self {
                ty: new_ty,
                lhs: Rc::new(AtomOrPart::Atom(self.clone())),
                op,
                rhs: Rc::new(rhs),
            }
        }
    }

    pub fn add_lhs(&self, op: RangeOp, lhs: AtomOrPart) -> Self {
        let new_ty = OpType::new(op);

        if self.ty >= new_ty {
            // keep ty
            Self {
                ty: self.ty,
                lhs: Rc::new(lhs),
                op,
                rhs: Rc::new(AtomOrPart::Atom(self.clone())),
            }
        } else {
            Self {
                ty: new_ty,
                lhs: Rc::new(lhs),
                op,
                rhs: Rc::new(AtomOrPart::Atom(self.clone())),
            }
        }
    }
}

pub static CONST_OPS: &[RangeOp] = &[RangeOp::Eq];
pub static DL_OPS: &[RangeOp] = &[
    RangeOp::Neq,
    RangeOp::Add(true),
    RangeOp::Add(false),
    RangeOp::Sub(true),
    RangeOp::Sub(false),
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
    RangeOp::And,
    RangeOp::Or,
];
pub static LIA_OPS: &[RangeOp] = &[
    RangeOp::Mul(true),
    RangeOp::Mul(false),
    RangeOp::Div(true),
    RangeOp::Div(false),
    RangeOp::Mod,
    RangeOp::Exp,
];

pub trait Atomize {
    fn atoms_or_part(&self, analyzer: &mut impl GraphBackend) -> AtomOrPart;
    fn atomize(&self, analyzer: &mut impl GraphBackend) -> Option<SolverAtom>;
}

impl Atomize for Elem<Concrete> {
    #[tracing::instrument(level = "trace", skip_all)]
    fn atoms_or_part(&self, analyzer: &mut impl GraphBackend) -> AtomOrPart {
        match self {
            Elem::Arena(_) => self.dearenaize(analyzer).borrow().atoms_or_part(analyzer),
            Elem::Concrete(_) | Elem::Reference(_) => AtomOrPart::Part(self.clone()),
            Elem::ConcreteDyn(_) => AtomOrPart::Part(self.clone()),
            Elem::Expr(expr) => {
                match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                    MaybeCollapsed::Concretes(_l, _r) => {
                        let exec_res = expr.exec_op(true, analyzer).unwrap();
                        return exec_res.atoms_or_part(analyzer);
                    }
                    MaybeCollapsed::Collapsed(elem) => {
                        return elem.atoms_or_part(analyzer);
                    }
                    MaybeCollapsed::Not(..) => {}
                }

                match (
                    expr.lhs.atoms_or_part(analyzer),
                    expr.rhs.atoms_or_part(analyzer),
                ) {
                    (ref lp @ AtomOrPart::Part(ref l), ref rp @ AtomOrPart::Part(ref r)) => {
                        // println!("part part");
                        match (l, r) {
                            (_, Elem::Arena(_)) => todo!(),
                            (Elem::Arena(_), _) => todo!(),
                            (Elem::Reference(Reference { .. }), Elem::Concrete(_))
                            | (Elem::Concrete(_), Elem::Reference(Reference { .. })) => {
                                let ty = OpType::new(expr.op);
                                let atom = SolverAtom {
                                    ty,
                                    lhs: Rc::new(lp.clone()),
                                    op: expr.op,
                                    rhs: Rc::new(rp.clone()),
                                };
                                AtomOrPart::Atom(atom)
                            }
                            (
                                Elem::Reference(Reference { .. }),
                                Elem::Reference(Reference { .. }),
                            ) => {
                                let ty = if DL_OPS.contains(&expr.op) {
                                    OpType::DL
                                } else if CONST_OPS.contains(&expr.op) {
                                    OpType::Const
                                } else {
                                    OpType::Other
                                };
                                let atom = SolverAtom {
                                    ty,
                                    lhs: Rc::new(lp.clone()),
                                    op: expr.op,
                                    rhs: Rc::new(rp.clone()),
                                };
                                AtomOrPart::Atom(atom)
                            }
                            (Elem::Expr(_), Elem::Expr(_)) => {
                                todo!("here");
                            }
                            (Elem::Expr(_), Elem::Reference(Reference { .. })) => {
                                todo!("here1");
                            }
                            (Elem::Reference(Reference { .. }), Elem::Expr(_)) => {
                                todo!("here2");
                            }
                            (Elem::Expr(_), Elem::Concrete(_)) => {
                                todo!("here3");
                            }
                            (Elem::Concrete(_), Elem::Expr(_)) => {
                                todo!("here4");
                            }
                            (Elem::Concrete(_), Elem::Concrete(_)) => {
                                let _ = expr.clone().arenaize(analyzer);
                                let res = expr.exec_op(true, analyzer).unwrap();
                                if res == Elem::Expr(expr.clone()) {
                                    AtomOrPart::Part(res)
                                } else {
                                    res.atoms_or_part(analyzer)
                                }
                            }
                            (Elem::ConcreteDyn(_), _) => AtomOrPart::Part(Elem::Null),
                            (_, Elem::ConcreteDyn(_)) => AtomOrPart::Part(Elem::Null),
                            (Elem::Null, _) => AtomOrPart::Part(Elem::Null),
                            (_, Elem::Null) => AtomOrPart::Part(Elem::Null),
                        }
                    }
                    (AtomOrPart::Atom(l_atom), r @ AtomOrPart::Part(_)) => {
                        // println!("atom part");

                        AtomOrPart::Atom(l_atom.add_rhs(expr.op, r))
                    }
                    (l @ AtomOrPart::Part(_), AtomOrPart::Atom(r_atom)) => {
                        // println!("part atom");
                        AtomOrPart::Atom(r_atom.add_lhs(expr.op, l))
                    }
                    (AtomOrPart::Atom(l_atoms), AtomOrPart::Atom(r_atoms)) => {
                        // println!("atom atom");
                        AtomOrPart::Atom(r_atoms.add_lhs(expr.op, AtomOrPart::Atom(l_atoms)))
                    }
                }
            }
            Elem::Null => AtomOrPart::Part(self.clone()),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn atomize(&self, analyzer: &mut impl GraphBackend) -> Option<SolverAtom> {
        use Elem::*;

        match self {
            Reference(_) => None,   //{ println!("was dyn"); None},
            Null => None,           //{ println!("was null"); None},
            Concrete(_c) => None,   //{ println!("was conc: {}", _c.val.as_human_string()); None },
            ConcreteDyn(_) => None, //{ println!("was concDyn"); None},
            Expr(_) => {
                // println!("atomized: was expr");
                let AtomOrPart::Atom(mut a) = self.atoms_or_part(analyzer) else {
                    // println!("returning none");
                    return None;
                };
                a.update_max_ty();
                Some(a)
            }
            Arena(_) => match &*self.dearenaize(analyzer).borrow() {
                e @ Expr(_) => {
                    let AtomOrPart::Atom(mut a) = e.atoms_or_part(analyzer) else {
                        // println!("returning none arena");
                        return None;
                    };
                    a.update_max_ty();
                    Some(a)
                }
                _ => None,
            },
        }
    }
}
