use ethers_core::types::H256;
use crate::NodeIdx;
use crate::GraphLike;
use crate::range::range_string::ToRangeString;
use crate::analyzer::AsDotStr;
use ethers_core::types::Address;
use crate::context::ContextNode;
use std::collections::BTreeMap;
use crate::range::elem_ty::Dynamic;
use crate::range::elem::RangeOp;
use crate::range::elem_ty::DynSide;
use crate::context::ContextVarNode;
use ethers_core::types::I256;
use ethers_core::types::U256;
use crate::range::elem_ty::RangeConcrete;
use crate::Builtin;
use crate::range::elem_ty::Elem;
use crate::range::elem::RangeElem;
use crate::Concrete;
use crate::analyzer::AnalyzerLike;

use solang_parser::pt::Loc;

pub mod elem;
pub mod elem_ty;
pub mod range_ops;
pub mod range_string;

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct SolcRange {
    pub min: Elem<Concrete>,
    pub max: Elem<Concrete>,
}

impl AsDotStr for SolcRange {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("[{}, {}]",
            self.min.eval(analyzer).to_range_string(analyzer).s,
            self.max.eval(analyzer).to_range_string(analyzer).s
        )
    }
}

impl From<bool> for SolcRange {
    fn from(b: bool) -> Self {
        let val = Elem::Concrete(RangeConcrete { val: Concrete::Bool(b), loc: Loc::Implicit });
        Self {
            min: val.clone(),
            max: val,
        }
    }
}


impl SolcRange {
    pub fn default_bool() -> Self {
        let min = Elem::Concrete(RangeConcrete { val: Concrete::Bool(false), loc: Loc::Implicit });
        let max = Elem::Concrete(RangeConcrete { val: Concrete::Bool(true), loc: Loc::Implicit });
        Self {
            min,
            max,
        }
    }
    pub fn from(c: Concrete) -> Option<Self> {
        match c {
            c @ Concrete::Uint(_, _)
            | c @ Concrete::Int(_, _)
            | c @ Concrete::Bool(_)
            | c @ Concrete::Address(_)
            | c @ Concrete::Bytes(_, _) => {
                Some(SolcRange {
                    min: Elem::Concrete(RangeConcrete { val: c.clone(), loc: Loc::Implicit }),
                    max: Elem::Concrete(RangeConcrete { val: c, loc: Loc::Implicit }),
                })
            }
            e => { println!("from: {:?}", e); None}
        }
    }
    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete { val: Concrete::Uint(*size, 0.into()), loc: Loc::Implicit }),
                        max: Elem::Concrete(RangeConcrete { val: Concrete::Uint(*size, U256::MAX), loc: Loc::Implicit }),
                    })
                } else {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete { val: Concrete::Uint(*size, 0.into()), loc: Loc::Implicit }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, U256::from(2).pow(U256::from(*size)) - 1),
                            loc: Loc::Implicit,
                        }),
                    })
                }
            }
            Builtin::Int(size) => {
                if *size == 256 {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete { val: Concrete::Int(*size, I256::MIN), loc: Loc::Implicit }),
                        max: Elem::Concrete(RangeConcrete { val: Concrete::Int(*size, I256::MAX), loc: Loc::Implicit }),
                    })
                } else {
                    let max: I256 =
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - 1.into();
                    let min = max * I256::from(-1i32);
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete { val: Concrete::Int(*size, min), loc: Loc::Implicit }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, max),
                            loc: Loc::Implicit,
                        }),
                    })
                }
            }
            Builtin::Bool => {
                Some(SolcRange {
                    min: Elem::Concrete(RangeConcrete { val: Concrete::Bool(false), loc: Loc::Implicit }),
                    max: Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: Loc::Implicit,
                    }),
                })
            },
            Builtin::Address => {
                Some(SolcRange {
                    min: Elem::Concrete(RangeConcrete { val: Concrete::Address(Address::from_slice(&[0x00; 20])), loc: Loc::Implicit }),
                    max: Elem::Concrete(RangeConcrete {
                        val: Concrete::Address(Address::from_slice(&[0xff; 20])),
                        loc: Loc::Implicit,
                    }),
                })
            },
            Builtin::Bytes(size) => {
                let v: Vec<_> = (0..32u8).map(|i| if i < *size { 0xff } else { 0x00 }).collect();
                Some(SolcRange {
                    min: Elem::Concrete(RangeConcrete { val: Concrete::Bytes(*size, H256::from_slice(&[0x00; 32])), loc: Loc::Implicit }),
                    max: Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(*size, H256::from_slice(&v[..])),
                        loc: Loc::Implicit,
                    }),
                })
            },
            _ => None,
        }
    }

    pub fn lte_dyn(self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min,
            max: self
                .max
                .min(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc))),
        }
    }

    pub fn gte_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc))),
            max: self.max,
        }
    }

    pub fn lt_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min,
            max: self
                .max
                .min(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)) - Elem::Concrete(RangeConcrete { val: U256::from(1).into(), loc: Loc::Implicit } )),
        }
    }

    pub fn gt_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)) + Elem::Concrete(RangeConcrete { val: U256::from(1).into(), loc: Loc::Implicit } )),
            max: self.max,
        }
    }

    pub fn dyn_fn_from_op(
        op: RangeOp,
    ) -> (
        &'static dyn Fn(SolcRange, ContextVarNode, (DynSide, DynSide), Loc) -> SolcRange,
        (DynSide, DynSide),
    ) {
        match op {
            RangeOp::Add => (
                &Self::add_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Sub => (
                &Self::sub_dyn,
                (DynSide::Max, DynSide::Min),
            ),
            RangeOp::Mul => (
                &Self::mul_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Div => (
                &Self::div_dyn,
                (DynSide::Max, DynSide::Min),
            ),
            RangeOp::Shr => (
                &Self::shr_dyn,
                (DynSide::Max, DynSide::Min),
            ),
            RangeOp::Shl => (
                &Self::shl_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Mod => (
                &Self::mod_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Min => (
                &Self::min_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Max => (
                &Self::max_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Lt => (
                &Self::lt_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Lte => (
                &Self::lte_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Gt => (
                &Self::gt_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Gte => (
                &Self::gte_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Eq => (
                &Self::eq_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Neq => (
                &Self::neq_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::Exp => (
                &Self::exp_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            RangeOp::BitAnd => (
                &Self::bit_and_dyn,
                (DynSide::Min, DynSide::Max),
            ),
            // RangeOp::And => (
            //     &Self::and_dyn,
            //     (DynSide::Min, DynSide::Max),
            // ),
            // RangeOp::Or => (
            //     &Self::or_dyn,
            //     (DynSide::Min, DynSide::Max),
            // ),
            e => unreachable!("Comparator operations shouldn't exist in a range: {:?}", e),
        }
    }

    pub fn add_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min + Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max + Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn sub_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min - Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max - Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn mul_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min * Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max * Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn exp_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min.pow(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc))),
            max: self.max.pow(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc))),
        }
    }

    pub fn bit_and_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min & Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max & Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn div_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min / Elem::from(Concrete::from(U256::from(1))).max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc))),
            max: self.max / Elem::from(Concrete::from(U256::from(1))).max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc))),
        }
    }

    pub fn shl_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min << Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max << Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn shr_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min >> Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)),
            max: self.max >> Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)),
        }
    }

    pub fn mod_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: Elem::from(Concrete::from(U256::zero())),
            max: Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)) - Elem::from(Concrete::from(U256::from(1)))
        }
    }

    pub fn min_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .min(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc))),
            max: self
                .max
                .min(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc))),
        }
    }

    pub fn max_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc))),
            max: self
                .max
                .max(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc))),
        }
    }

    pub fn eq_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        let min = self
                .min
                .eq(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)));
        let max = self
                .max
                .eq(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)));
        Self {
            min: min.clone().max(max.clone()),
            max: min.max(max),
        }
    }

    pub fn neq_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynSide, DynSide),
        loc: Loc,
    ) -> Self {
        let min = self
                .min
                .neq(Elem::Dynamic(Dynamic::new(other.into(), range_sides.0, loc)));
        let max = self
                .max
                .neq(Elem::Dynamic(Dynamic::new(other.into(), range_sides.1, loc)));
        Self {
            min: min.clone().max(max.clone()),
            max: min.max(max),
        }
    }
}


impl Range<Concrete> for SolcRange {
    type ElemTy = Elem<Concrete>;
    fn range_min(&self) -> Self::ElemTy {
        self.min.clone()
    }
    fn range_max(&self) -> Self::ElemTy {
        self.max.clone()
    }
    fn set_range_min(&mut self, new: Self::ElemTy) {
        self.min = new;
    }
    fn set_range_max(&mut self, new: Self::ElemTy) {
        self.max = new;
    }
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy) {
        self.min.filter_recursion(self_idx, old);
    }
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy) {
        self.max.filter_recursion(self_idx, old);
    }
}

pub trait Range<T> {
    type ElemTy: RangeElem<T> + Clone;
    fn range_min(&self) -> Self::ElemTy;
    fn range_max(&self) -> Self::ElemTy;
    fn set_range_min(&mut self, new: Self::ElemTy);
    fn set_range_max(&mut self, new: Self::ElemTy);
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy);
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy);
    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.range_min().dependent_on();
        deps.extend(self.range_max().dependent_on());
        deps
    }

    fn update_deps(&mut self, ctx: ContextNode, analyzer: &impl GraphLike) {
        let deps = self.dependent_on();
        let mapping: BTreeMap<ContextVarNode, ContextVarNode> = deps.into_iter().map(|dep| {
            (dep, dep.latest_version_in_ctx(ctx, analyzer))
        }).collect();

        let mut min = self.range_min();
        let mut max = self.range_max();
        min.update_deps(&mapping);
        max.update_deps(&mapping);
        self.set_range_min(min);
        self.set_range_max(max);
    }
}

pub trait RangeEval<E, T: RangeElem<E>>: Range<E, ElemTy = T> {
    fn sat(&self, analyzer: &impl AnalyzerLike) -> bool;
    fn unsat(&self, analyzer: &impl AnalyzerLike) -> bool {
        !self.sat(analyzer)
    }
    fn contains(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool;
}

impl RangeEval<Concrete, Elem<Concrete>> for SolcRange {
    fn sat(&self, analyzer: &impl AnalyzerLike) -> bool {
        matches!(self
            .range_min()
            .eval(analyzer)
            .range_ord(&self.range_max().eval(analyzer)), None | Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal))
    }

    fn contains(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        let min_contains = matches!(self
            .range_min()
            .eval(analyzer)
            .range_ord(&other.range_min().eval(analyzer)), Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal));

        let max_contains = matches!(self
            .range_max()
            .eval(analyzer)
            .range_ord(&other.range_max().eval(analyzer)), Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal));

        min_contains && max_contains
    }
}

#[cfg(test)]
mod tests {
    

    #[test]
    fn it_works() {

    }
}
