use crate::analyzer::AnalyzerLike;
use crate::analyzer::AsDotStr;
use crate::context::ContextNode;
use crate::context::ContextVarNode;
use crate::range::elem::RangeElem;
use crate::range::elem::RangeOp;
use crate::range::elem_ty::Dynamic;
use crate::range::elem_ty::Elem;
use crate::range::elem_ty::RangeConcrete;
use crate::range::elem_ty::RangeDyn;
use crate::range::range_string::ToRangeString;
use crate::Builtin;
use crate::Concrete;
use crate::GraphLike;
use crate::NodeIdx;
use ethers_core::types::Address;
use ethers_core::types::H256;
use ethers_core::types::I256;
use ethers_core::types::U256;
use std::collections::BTreeMap;

use solang_parser::pt::Loc;

pub mod elem;
pub mod elem_ty;
pub mod range_ops;
pub mod range_string;

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct SolcRange {
    pub min: Elem<Concrete>,
    pub max: Elem<Concrete>,
    pub exclusions: Vec<Elem<Concrete>>,
}

impl AsDotStr for SolcRange {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        // println!("here: {}", self.exclusions.iter().map(|excl| excl.as_dot_str(analyzer)).collect::<Vec<_>>().join(", "));
        format!(
            "[{}, {}] excluding: [{}]",
            self.evaled_range_min(analyzer)
                .to_range_string(false, analyzer)
                .s,
            self.evaled_range_max(analyzer)
                .to_range_string(true, analyzer)
                .s,
            self.exclusions
                .iter()
                .map(|excl| excl.to_range_string(false, analyzer).s)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl From<bool> for SolcRange {
    fn from(b: bool) -> Self {
        let val = Elem::Concrete(RangeConcrete {
            val: Concrete::Bool(b),
            loc: Loc::Implicit,
        });
        Self {
            min: val.clone(),
            max: val,
            exclusions: vec![],
        }
    }
}

impl SolcRange {
    pub fn min_is_negative(&self, analyzer: &impl GraphLike) -> bool {
        self.min.is_negative(false, analyzer)
    }

    pub fn default_bool() -> Self {
        let min = Elem::Concrete(RangeConcrete {
            val: Concrete::Bool(false),
            loc: Loc::Implicit,
        });
        let max = Elem::Concrete(RangeConcrete {
            val: Concrete::Bool(true),
            loc: Loc::Implicit,
        });
        Self {
            min,
            max,
            exclusions: vec![],
        }
    }
    pub fn from(c: Concrete) -> Option<Self> {
        match c {
            c @ Concrete::Uint(_, _)
            | c @ Concrete::Int(_, _)
            | c @ Concrete::Bool(_)
            | c @ Concrete::Address(_)
            | c @ Concrete::Bytes(_, _) => Some(SolcRange {
                min: Elem::Concrete(RangeConcrete {
                    val: c.clone(),
                    loc: Loc::Implicit,
                }),
                max: Elem::Concrete(RangeConcrete {
                    val: c,
                    loc: Loc::Implicit,
                }),
                exclusions: vec![],
            }),
            Concrete::DynBytes(b) => {
                let val = b
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                let r = Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: Elem::from(Concrete::from(U256::from(b.len()))),
                    val,
                    loc: Loc::Implicit,
                }));
                Some(SolcRange {
                    min: r.clone(),
                    max: r,
                    exclusions: vec![],
                })
            }
            e => {
                println!("from: {:?}", e);
                None
            }
        }
    }
    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, 0.into()),
                            loc: Loc::Implicit,
                        }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, U256::MAX),
                            loc: Loc::Implicit,
                        }),
                        exclusions: vec![],
                    })
                } else {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, 0.into()),
                            loc: Loc::Implicit,
                        }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, U256::from(2).pow(U256::from(*size)) - 1),
                            loc: Loc::Implicit,
                        }),
                        exclusions: vec![],
                    })
                }
            }
            Builtin::Int(size) => {
                if *size == 256 {
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, I256::MIN),
                            loc: Loc::Implicit,
                        }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, I256::MAX),
                            loc: Loc::Implicit,
                        }),
                        exclusions: vec![],
                    })
                } else {
                    let max: I256 =
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - 1.into();
                    let min = max * I256::from(-1i32);
                    Some(SolcRange {
                        min: Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, min),
                            loc: Loc::Implicit,
                        }),
                        max: Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, max),
                            loc: Loc::Implicit,
                        }),
                        exclusions: vec![],
                    })
                }
            }
            Builtin::Bool => Some(SolcRange {
                min: Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(false),
                    loc: Loc::Implicit,
                }),
                max: Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(true),
                    loc: Loc::Implicit,
                }),
                exclusions: vec![],
            }),
            Builtin::Address => Some(SolcRange {
                min: Elem::Concrete(RangeConcrete {
                    val: Concrete::Address(Address::from_slice(&[0x00; 20])),
                    loc: Loc::Implicit,
                }),
                max: Elem::Concrete(RangeConcrete {
                    val: Concrete::Address(Address::from_slice(&[0xff; 20])),
                    loc: Loc::Implicit,
                }),
                exclusions: vec![],
            }),
            Builtin::Bytes(size) => {
                let v: Vec<_> = (0..32u8)
                    .map(|i| if i < *size { 0xff } else { 0x00 })
                    .collect();
                Some(SolcRange {
                    min: Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(*size, H256::from_slice(&[0x00; 32])),
                        loc: Loc::Implicit,
                    }),
                    max: Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(*size, H256::from_slice(&v[..])),
                        loc: Loc::Implicit,
                    }),
                    exclusions: vec![],
                })
            }
            Builtin::DynamicBytes | Builtin::String | Builtin::Array(_) => Some(SolcRange {
                min: Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: Elem::from(Concrete::from(U256::zero())),
                    val: Default::default(),
                    loc: Loc::Implicit,
                })),
                max: Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: Elem::from(Concrete::from(U256::MAX)),
                    val: Default::default(),
                    loc: Loc::Implicit,
                })),
                exclusions: vec![],
            }),
            _ => None,
        }
    }

    pub fn lte_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min,
            max: self.max.min(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            exclusions: self.exclusions,
        }
    }

    pub fn gte_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min.max(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            max: self.max,
            exclusions: self.exclusions,
        }
    }

    pub fn lt_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min,
            max: self.max.min(
                Elem::Dynamic(Dynamic::new(other.into(), loc))
                    - Elem::Concrete(RangeConcrete {
                        val: U256::from(1).into(),
                        loc: Loc::Implicit,
                    }),
            ),
            exclusions: self.exclusions,
        }
    }

    pub fn gt_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min.max(
                Elem::Dynamic(Dynamic::new(other.into(), loc))
                    + Elem::Concrete(RangeConcrete {
                        val: U256::from(1).into(),
                        loc: Loc::Implicit,
                    }),
            ),
            max: self.max,
            exclusions: self.exclusions,
        }
    }

    pub fn dyn_fn_from_op(
        op: RangeOp,
    ) -> &'static dyn Fn(SolcRange, ContextVarNode, Loc) -> SolcRange {
        match op {
            RangeOp::Add => &Self::add_dyn,
            RangeOp::Sub => &Self::sub_dyn,
            RangeOp::Mul => &Self::mul_dyn,
            RangeOp::Div => &Self::div_dyn,
            RangeOp::Shr => &Self::shr_dyn,
            RangeOp::Shl => &Self::shl_dyn,
            RangeOp::Mod => &Self::mod_dyn,
            RangeOp::Min => &Self::min_dyn,
            RangeOp::Max => &Self::max_dyn,
            RangeOp::Lt => &Self::lt_dyn,
            RangeOp::Lte => &Self::lte_dyn,
            RangeOp::Gt => &Self::gt_dyn,
            RangeOp::Gte => &Self::gte_dyn,
            RangeOp::Eq => &Self::eq_dyn,
            RangeOp::Neq => &Self::neq_dyn,
            RangeOp::Exp => &Self::exp_dyn,
            RangeOp::BitAnd => &Self::bit_and_dyn,
            RangeOp::BitOr => &Self::bit_or_dyn,
            RangeOp::BitXor => &Self::bit_xor_dyn,
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

    pub fn add_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min + Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max + Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn sub_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min - Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max - Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn mul_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min * Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max * Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn exp_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min.pow(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            max: self.max.pow(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            exclusions: self.exclusions,
        }
    }

    pub fn bit_and_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min & Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max & Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn bit_or_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min | Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max | Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn bit_xor_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min ^ Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max ^ Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn div_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        let elem = Elem::Dynamic(Dynamic::new(other.into(), loc));
        Self {
            min: self.min / elem.clone(),
            max: self.max / elem,
            exclusions: self.exclusions,
        }
    }

    pub fn shl_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min << Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max << Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn shr_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min >> Elem::Dynamic(Dynamic::new(other.into(), loc)),
            max: self.max >> Elem::Dynamic(Dynamic::new(other.into(), loc)),
            exclusions: self.exclusions,
        }
    }

    pub fn mod_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        let elem = Elem::Dynamic(Dynamic::new(other.into(), loc));
        Self {
            min: Elem::from(Concrete::from(U256::zero())),
            max: elem.clone() - Elem::from(Concrete::from(U256::from(1))).cast(elem),
            exclusions: self.exclusions,
        }
    }

    pub fn min_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min.min(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            max: self.max.min(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            exclusions: self.exclusions,
        }
    }

    pub fn max_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        Self {
            min: self.min.max(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            max: self.max.max(Elem::Dynamic(Dynamic::new(other.into(), loc))),
            exclusions: self.exclusions,
        }
    }

    pub fn eq_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        let min = self.min.eq(Elem::Dynamic(Dynamic::new(other.into(), loc)));
        let max = self.max.eq(Elem::Dynamic(Dynamic::new(other.into(), loc)));
        Self {
            min: min.clone().max(max.clone()),
            max: min.max(max),
            exclusions: self.exclusions,
        }
    }

    pub fn neq_dyn(self, other: ContextVarNode, loc: Loc) -> Self {
        let min = self.min.neq(Elem::Dynamic(Dynamic::new(other.into(), loc)));
        let max = self.max.neq(Elem::Dynamic(Dynamic::new(other.into(), loc)));
        Self {
            min: min.clone().max(max.clone()),
            max: min.max(max),
            exclusions: self.exclusions,
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
    fn evaled_range_min(&self, analyzer: &impl GraphLike) -> Self::ElemTy {
        self.range_min().minimize(analyzer)
    }
    fn evaled_range_max(&self, analyzer: &impl GraphLike) -> Self::ElemTy {
        self.range_max().maximize(analyzer)
    }
    fn simplified_range_min(&self, analyzer: &impl GraphLike) -> Self::ElemTy {
        self.range_min().simplify_minimize(analyzer)
    }
    fn simplified_range_max(&self, analyzer: &impl GraphLike) -> Self::ElemTy {
        self.range_max().simplify_maximize(analyzer)
    }
    fn range_exclusions(&self) -> Vec<Self::ElemTy> {
        self.exclusions.clone()
    }
    fn set_range_min(&mut self, new: Self::ElemTy) {
        self.min = new;
    }
    fn set_range_max(&mut self, new: Self::ElemTy) {
        self.max = new;
    }
    fn set_range_exclusions(&mut self, new: Vec<Self::ElemTy>) {
        self.exclusions = new;
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
    fn evaled_range_min(&self, analyzer: &impl GraphLike) -> Self::ElemTy;
    fn evaled_range_max(&self, analyzer: &impl GraphLike) -> Self::ElemTy;
    fn simplified_range_min(&self, analyzer: &impl GraphLike) -> Self::ElemTy;
    fn simplified_range_max(&self, analyzer: &impl GraphLike) -> Self::ElemTy;
    fn range_min(&self) -> Self::ElemTy;
    fn range_max(&self) -> Self::ElemTy;
    fn range_exclusions(&self) -> Vec<Self::ElemTy>
    where
        Self: std::marker::Sized;
    fn set_range_min(&mut self, new: Self::ElemTy);
    fn set_range_max(&mut self, new: Self::ElemTy);
    fn set_range_exclusions(&mut self, new: Vec<Self::ElemTy>)
    where
        Self: std::marker::Sized;
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy);
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, old: Self::ElemTy);
    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.range_min().dependent_on();
        deps.extend(self.range_max().dependent_on());
        deps
    }

    fn update_deps(&mut self, ctx: ContextNode, analyzer: &impl GraphLike) {
        let deps = self.dependent_on();
        let mapping: BTreeMap<ContextVarNode, ContextVarNode> = deps
            .into_iter()
            .filter(|dep| !dep.is_const(analyzer))
            .map(|dep| (dep, dep.latest_version_in_ctx(ctx, analyzer)))
            .collect();

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
    fn contains_elem(&self, other: &T, analyzer: &impl AnalyzerLike) -> bool;
    fn overlaps(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool;
}

impl RangeEval<Concrete, Elem<Concrete>> for SolcRange {
    fn sat(&self, analyzer: &impl AnalyzerLike) -> bool {
        matches!(
            self.evaled_range_min(analyzer)
                .range_ord(&self.evaled_range_max(analyzer)),
            None | Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        )
    }

    fn contains(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        let min_contains = matches!(
            self.evaled_range_min(analyzer)
                .range_ord(&other.evaled_range_min(analyzer)),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        let max_contains = matches!(
            self.evaled_range_max(analyzer)
                .range_ord(&other.evaled_range_max(analyzer)),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains && max_contains
    }

    fn contains_elem(&self, other: &Elem<Concrete>, analyzer: &impl AnalyzerLike) -> bool {
        // println!(
        //     "min: {:?}, other_min: {:?}, ord: {:?}",
        //     self.evaled_range_min(analyzer),
        //     other.minimize(analyzer),
        //     self.evaled_range_min(analyzer).range_ord(&other.minimize(analyzer))
        // );
        let min_contains = matches!(
            self.evaled_range_min(analyzer)
                .range_ord(&other.minimize(analyzer)),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        // println!(
        //     "max: {:?}, other_max: {:?}, ord: {:?}",
        //     self.evaled_range_max(analyzer),
        //     other.maximize(analyzer),
        //     self.evaled_range_max(analyzer).range_ord(&other.maximize(analyzer))
        // );

        let max_contains = matches!(
            self.evaled_range_max(analyzer)
                .range_ord(&other.maximize(analyzer)),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains && max_contains
    }

    fn overlaps(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        let min_contains = matches!(
            self.evaled_range_min(analyzer)
                .range_ord(&other.evaled_range_min(analyzer)),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        let max_contains = matches!(
            self.evaled_range_max(analyzer)
                .range_ord(&other.evaled_range_max(analyzer)),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains || max_contains
    }
}
