use crate::analyzer::AsDotStr;
use crate::analyzer::GraphError;
use crate::analyzer::GraphLike;
use crate::context::ContextNode;
use crate::context::ContextVarNode;
use crate::range::elem::RangeElem;
use crate::range::elem::RangeOp;

use crate::range::elem_ty::Elem;
use crate::range::elem_ty::RangeConcrete;
use crate::range::elem_ty::RangeDyn;
use crate::range::range_string::ToRangeString;
use crate::Builtin;
use crate::Concrete;

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
    pub min_cached: Option<Elem<Concrete>>,
    pub max: Elem<Concrete>,
    pub max_cached: Option<Elem<Concrete>>,
    pub exclusions: Vec<Elem<Concrete>>,
}

impl AsDotStr for SolcRange {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        // println!("here: {}", self.exclusions.iter().map(|excl| excl.as_dot_str(analyzer)).collect::<Vec<_>>().join(", "));
        format!(
            "[{}, {}] excluding: [{}]",
            self.evaled_range_min(analyzer)
                .unwrap()
                .to_range_string(false, analyzer)
                .s,
            self.evaled_range_max(analyzer)
                .unwrap()
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
        Self::new(val.clone(), val, vec![])
    }
}

impl SolcRange {
    pub fn new(min: Elem<Concrete>, max: Elem<Concrete>, exclusions: Vec<Elem<Concrete>>) -> Self {
        Self {
            min,
            min_cached: None,
            max,
            max_cached: None,
            exclusions,
        }
    }

    pub fn min_is_negative(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
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
        Self::new(min, max, vec![])
    }
    pub fn from(c: Concrete) -> Option<Self> {
        match c {
            c @ Concrete::Uint(_, _)
            | c @ Concrete::Int(_, _)
            | c @ Concrete::Bool(_)
            | c @ Concrete::Address(_)
            | c @ Concrete::Bytes(_, _) => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete {
                    val: c.clone(),
                    loc: Loc::Implicit,
                }),
                Elem::Concrete(RangeConcrete {
                    val: c,
                    loc: Loc::Implicit,
                }),
                vec![],
            )),
            Concrete::String(s) => {
                let val = s
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                let r = Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::from(s.len()))),
                    val,
                    loc: Loc::Implicit,
                }));
                Some(SolcRange::new(r.clone(), r, vec![]))
            }
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
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::from(b.len()))),
                    val,
                    loc: Loc::Implicit,
                }));
                Some(SolcRange::new(r.clone(), r, vec![]))
            }
            _e => {
                // println!("from: {e:?}");
                None
            }
        }
    }

    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, 0.into()),
                            loc: Loc::Implicit,
                        }),
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, U256::MAX),
                            loc: Loc::Implicit,
                        }),
                        vec![],
                    ))
                } else {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, 0.into()),
                            loc: Loc::Implicit,
                        }),
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*size, U256::from(2).pow(U256::from(*size)) - 1),
                            loc: Loc::Implicit,
                        }),
                        vec![],
                    ))
                }
            }
            Builtin::Int(size) => {
                if *size == 256 {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, I256::MIN),
                            loc: Loc::Implicit,
                        }),
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, I256::MAX),
                            loc: Loc::Implicit,
                        }),
                        vec![],
                    ))
                } else {
                    let max: I256 =
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::from(1);
                    let min = max * I256::from(-1i32) - I256::from(1i32);
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, min),
                            loc: Loc::Implicit,
                        }),
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*size, max),
                            loc: Loc::Implicit,
                        }),
                        vec![],
                    ))
                }
            }
            Builtin::Bool => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(false),
                    loc: Loc::Implicit,
                }),
                Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(true),
                    loc: Loc::Implicit,
                }),
                vec![],
            )),
            Builtin::Address | Builtin::Payable | Builtin::AddressPayable => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete {
                    val: Concrete::Address(Address::from_slice(&[0x00; 20])),
                    loc: Loc::Implicit,
                }),
                Elem::Concrete(RangeConcrete {
                    val: Concrete::Address(Address::from_slice(&[0xff; 20])),
                    loc: Loc::Implicit,
                }),
                vec![],
            )),
            Builtin::Bytes(size) => {
                let v: Vec<_> = (0..32u8)
                    .map(|i| if i < *size { 0xff } else { 0x00 })
                    .collect();
                Some(SolcRange::new(
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(*size, H256::from_slice(&[0x00; 32])),
                        loc: Loc::Implicit,
                    }),
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(*size, H256::from_slice(&v[..])),
                        loc: Loc::Implicit,
                    }),
                    vec![],
                ))
            }
            Builtin::DynamicBytes
            | Builtin::String
            | Builtin::Array(_)
            | Builtin::Mapping(_, _) => Some(SolcRange::new(
                Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::zero())),
                    val: Default::default(),
                    loc: Loc::Implicit,
                })),
                Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::MAX)),
                    val: Default::default(),
                    loc: Loc::Implicit,
                })),
                vec![],
            )),
            _ => None,
        }
    }

    pub fn lte_dyn(self, other: ContextVarNode) -> Self {
        Self::new(self.min, self.max.min(Elem::from(other)), self.exclusions)
    }

    pub fn gte_dyn(self, other: ContextVarNode) -> Self {
        Self::new(self.min.max(Elem::from(other)), self.max, self.exclusions)
    }

    pub fn lt_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min,
            self.max.min(
                Elem::from(other)
                    - Elem::Concrete(RangeConcrete {
                        val: U256::from(1).into(),
                        loc: Loc::Implicit,
                    }),
            ),
            self.exclusions,
        )
    }

    pub fn gt_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.max(
                Elem::from(other)
                    + Elem::Concrete(RangeConcrete {
                        val: U256::from(1).into(),
                        loc: Loc::Implicit,
                    }),
            ),
            self.max,
            self.exclusions,
        )
    }

    pub fn dyn_fn_from_op(op: RangeOp) -> &'static dyn Fn(SolcRange, ContextVarNode) -> SolcRange {
        match op {
            RangeOp::Add(false) => &Self::add_dyn,
            RangeOp::Add(true) => &Self::wrapping_add_dyn,
            RangeOp::Sub(false) => &Self::sub_dyn,
            RangeOp::Sub(true) => &Self::wrapping_sub_dyn,
            RangeOp::Mul(false) => &Self::mul_dyn,
            RangeOp::Mul(true) => &Self::wrapping_mul_dyn,
            RangeOp::Div(..) => &Self::div_dyn,
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

    pub fn add_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min + Elem::from(other),
            self.max + Elem::from(other),
            self.exclusions,
        )
    }

    pub fn wrapping_add_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.wrapping_add(Elem::from(other)),
            self.max.wrapping_add(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn sub_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min - Elem::from(other),
            self.max - Elem::from(other),
            self.exclusions,
        )
    }

    pub fn wrapping_sub_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.wrapping_sub(Elem::from(other)),
            self.max.wrapping_sub(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn mul_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min * Elem::from(other),
            self.max * Elem::from(other),
            self.exclusions,
        )
    }

    pub fn wrapping_mul_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.wrapping_mul(Elem::from(other)),
            self.max.wrapping_mul(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn exp_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.pow(Elem::from(other)),
            self.max.pow(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn bit_and_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min & Elem::from(other),
            self.max & Elem::from(other),
            self.exclusions,
        )
    }

    pub fn bit_or_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min | Elem::from(other),
            self.max | Elem::from(other),
            self.exclusions,
        )
    }

    pub fn bit_xor_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min ^ Elem::from(other),
            self.max ^ Elem::from(other),
            self.exclusions,
        )
    }

    pub fn div_dyn(self, other: ContextVarNode) -> Self {
        let elem = Elem::from(other);
        Self::new(self.min / elem.clone(), self.max / elem, self.exclusions)
    }

    pub fn shl_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min << Elem::from(other),
            self.max << Elem::from(other),
            self.exclusions,
        )
    }

    pub fn shr_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min >> Elem::from(other),
            self.max >> Elem::from(other),
            self.exclusions,
        )
    }

    pub fn mod_dyn(self, other: ContextVarNode) -> Self {
        let elem = Elem::from(other);
        Self::new(
            Elem::from(Concrete::from(U256::zero())),
            elem.clone() - Elem::from(Concrete::from(U256::from(1))).cast(elem),
            self.exclusions,
        )
    }

    pub fn min_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.min(Elem::from(other)),
            self.max.min(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn max_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.max(Elem::from(other)),
            self.max.max(Elem::from(other)),
            self.exclusions,
        )
    }

    pub fn eq_dyn(self, other: ContextVarNode) -> Self {
        let min = self.min.eq(Elem::from(other));
        let max = self.max.eq(Elem::from(other));
        Self::new(min.clone().max(max.clone()), min.max(max), self.exclusions)
    }

    pub fn neq_dyn(self, other: ContextVarNode) -> Self {
        let min = self.min.neq(Elem::from(other));
        let max = self.max.neq(Elem::from(other));
        Self::new(min.clone().max(max.clone()), min.max(max), self.exclusions)
    }
}

impl Range<Concrete> for SolcRange {
    type ElemTy = Elem<Concrete>;
    fn range_min(&self) -> std::borrow::Cow<'_, Self::ElemTy> {
        std::borrow::Cow::Borrowed(&self.min)
    }
    fn range_max(&self) -> std::borrow::Cow<'_, Self::ElemTy> {
        std::borrow::Cow::Borrowed(&self.max)
    }
    fn range_min_mut(&mut self) -> &mut Self::ElemTy {
        &mut self.min
    }
    fn range_max_mut(&mut self) -> &mut Self::ElemTy {
        &mut self.max
    }

    fn cache_eval(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        if self.min_cached.is_none() {
            let min = self.range_min_mut();
            min.cache_minimize(analyzer)?;
            self.min_cached = Some(self.range_min().minimize(analyzer)?);
        }
        if self.max_cached.is_none() {
            let max = self.range_max_mut();
            max.cache_maximize(analyzer)?;
            self.max_cached = Some(self.range_max().maximize(analyzer)?);
        }
        Ok(())
    }

    fn evaled_range_min(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError> {
        if let Some(cached) = &self.min_cached {
            Ok(cached.clone())
        } else {
            self.range_min().minimize(analyzer)
        }
    }

    fn evaled_range_max(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError> {
        if let Some(cached) = &self.max_cached {
            Ok(cached.clone())
        } else {
            self.range_max().maximize(analyzer)
        }
    }

    fn simplified_range_min(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError> {
        self.range_min().simplify_minimize(analyzer)
    }
    fn simplified_range_max(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError> {
        self.range_max().simplify_maximize(analyzer)
    }
    fn range_exclusions(&self) -> Vec<Self::ElemTy> {
        self.exclusions.clone()
    }
    fn set_range_min(&mut self, new: Self::ElemTy) {
        self.min_cached = None;
        self.min = new;
    }
    fn set_range_max(&mut self, new: Self::ElemTy) {
        self.max_cached = None;
        self.max = new;
    }

    fn add_range_exclusion(&mut self, new: Self::ElemTy) {
        if !self.exclusions.contains(&new) {
            self.exclusions.push(new);
        }
    }
    fn set_range_exclusions(&mut self, new: Vec<Self::ElemTy>) {
        self.exclusions = new;
    }
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx) {
        self.min.filter_recursion(self_idx, new_idx);
    }
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx) {
        self.max.filter_recursion(self_idx, new_idx);
    }
}

pub trait Range<T> {
    type ElemTy: RangeElem<T> + Clone;
    fn cache_eval(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError>;
    fn evaled_range_min(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    fn evaled_range_max(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    fn simplified_range_min(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    fn simplified_range_max(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    fn range_min(&self) -> std::borrow::Cow<'_, Self::ElemTy>;
    fn range_max(&self) -> std::borrow::Cow<'_, Self::ElemTy>;
    fn uncache_range_min(&mut self) {
        self.range_min_mut().uncache();
    }
    fn uncache_range_max(&mut self) {
        self.range_max_mut().uncache();
    }
    fn range_min_mut(&mut self) -> &mut Self::ElemTy;
    fn range_max_mut(&mut self) -> &mut Self::ElemTy;
    fn range_exclusions(&self) -> Vec<Self::ElemTy>
    where
        Self: std::marker::Sized;
    fn set_range_min(&mut self, new: Self::ElemTy);
    fn set_range_max(&mut self, new: Self::ElemTy);
    fn set_range_exclusions(&mut self, new: Vec<Self::ElemTy>)
    where
        Self: std::marker::Sized;
    fn add_range_exclusion(&mut self, new: Self::ElemTy)
    where
        Self: std::marker::Sized;
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx);
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx);
    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.range_min().dependent_on();
        deps.extend(self.range_max().dependent_on());
        deps
    }

    fn update_deps(&mut self, node: ContextVarNode, ctx: ContextNode, analyzer: &impl GraphLike) {
        let deps = self.dependent_on();
        let mapping: BTreeMap<ContextVarNode, ContextVarNode> = deps
            .into_iter()
            .filter(|dep| !dep.is_const(analyzer).unwrap())
            .map(|dep| {
                let latest = dep.latest_version_in_ctx(ctx, analyzer).unwrap();
                if latest == node {
                    if let Some(prev) = latest.previous_version(analyzer) {
                        (dep, prev)
                    } else {
                        (dep, dep)
                    }
                } else {
                    (dep, latest)
                }
            })
            .collect();

        let mut min = self.range_min().into_owned();
        let mut max = self.range_max().into_owned();
        min.update_deps(&mapping);
        max.update_deps(&mapping);
        self.set_range_min(min);
        self.set_range_max(max);
    }
}

pub trait RangeEval<E, T: RangeElem<E>>: Range<E, ElemTy = T> {
    fn sat(&self, analyzer: &impl GraphLike) -> bool;
    fn unsat(&self, analyzer: &impl GraphLike) -> bool {
        !self.sat(analyzer)
    }
    fn contains(&self, other: &Self, analyzer: &impl GraphLike) -> bool;
    fn contains_elem(&self, other: &T, analyzer: &impl GraphLike) -> bool;
    fn overlaps(&self, other: &Self, analyzer: &impl GraphLike) -> bool;
}

impl RangeEval<Concrete, Elem<Concrete>> for SolcRange {
    fn sat(&self, analyzer: &impl GraphLike) -> bool {
        matches!(
            self.evaled_range_min(analyzer)
                .unwrap()
                .range_ord(&self.evaled_range_max(analyzer).unwrap()),
            None | Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        )
    }

    fn contains(&self, other: &Self, analyzer: &impl GraphLike) -> bool {
        let min_contains = matches!(
            self.evaled_range_min(analyzer)
                .unwrap()
                .range_ord(&other.evaled_range_min(analyzer).unwrap()),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        let max_contains = matches!(
            self.evaled_range_max(analyzer)
                .unwrap()
                .range_ord(&other.evaled_range_max(analyzer).unwrap()),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains && max_contains
    }

    fn contains_elem(&self, other: &Elem<Concrete>, analyzer: &impl GraphLike) -> bool {
        let min_contains = matches!(
            self.evaled_range_min(analyzer)
                .unwrap()
                .range_ord(&other.minimize(analyzer).unwrap()),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        let max_contains = matches!(
            self.evaled_range_max(analyzer)
                .unwrap()
                .range_ord(&other.maximize(analyzer).unwrap()),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains && max_contains
    }

    fn overlaps(&self, other: &Self, analyzer: &impl GraphLike) -> bool {
        let lhs_min = self.evaled_range_min(analyzer).unwrap();
        let rhs_max = other.evaled_range_max(analyzer).unwrap();

        match lhs_min.range_ord(&rhs_max) {
            Some(std::cmp::Ordering::Less) => {
                // we know our min is less than the other max
                // check that the max is greater than or eq their min
                let lhs_max = self.evaled_range_max(analyzer).unwrap();
                let rhs_min = other.evaled_range_min(analyzer).unwrap();
                matches!(
                    lhs_max.range_ord(&rhs_min),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                )
            }
            Some(std::cmp::Ordering::Equal) => true,
            _ => false,
        }
    }
}
