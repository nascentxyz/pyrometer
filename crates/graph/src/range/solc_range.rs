use crate::{
    nodes::{Builtin, Concrete, ContextVarNode},
    range::{elem::*, range_string::*, Range, RangeEval},
    AsDotStr, GraphBackend,
};

use shared::{GraphError, NodeIdx, RangeArena};

use ethers_core::types::{Address, H256, I256, U256};
use solang_parser::pt::Loc;

use std::{borrow::Cow, collections::BTreeMap};

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct FlattenedRange {
    pub min: Elem<Concrete>,
    pub max: Elem<Concrete>,
    pub exclusions: Vec<Elem<Concrete>>,
}

impl From<FlattenedRange> for SolcRange {
    fn from(range: FlattenedRange) -> Self {
        SolcRange::new(range.min, range.max, range.exclusions)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct SolcRange {
    pub min: Elem<Concrete>,
    pub min_cached: Option<usize>,
    pub max: Elem<Concrete>,
    pub max_cached: Option<usize>,
    pub exclusions: Vec<Elem<Concrete>>,
    pub flattened: Option<FlattenedRange>,
}

impl AsDotStr for SolcRange {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        format!(
            "[{}, {}] excluding: [{}]",
            self.evaled_range_min(analyzer, arena)
                .unwrap()
                .to_range_string(false, analyzer, arena)
                .s,
            self.evaled_range_max(analyzer, arena)
                .unwrap()
                .to_range_string(true, analyzer, arena)
                .s,
            self.exclusions
                .iter()
                .map(|excl| excl.to_range_string(false, analyzer, arena).s)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl From<bool> for SolcRange {
    fn from(b: bool) -> Self {
        let val = Elem::Concrete(RangeConcrete::new(Concrete::Bool(b), Loc::Implicit));
        Self::new(val.clone(), val, vec![])
    }
}

impl From<Elem<Concrete>> for SolcRange {
    fn from(elem: Elem<Concrete>) -> Self {
        Self::new(elem.clone(), elem, vec![])
    }
}

impl SolcRange {
    /// Get all ContextVarNodes that this range references
    pub fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        let mut deps = self.range_min().dependent_on(analyzer, arena);
        deps.extend(self.range_max().dependent_on(analyzer, arena));
        deps.dedup();

        deps.into_iter().map(ContextVarNode::from).collect()
    }

    pub fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps = self.range_min().recursive_dependent_on(analyzer, arena)?;
        deps.extend(self.range_max().recursive_dependent_on(analyzer, arena)?);
        deps.dedup();

        Ok(deps)
    }

    pub fn new(min: Elem<Concrete>, max: Elem<Concrete>, exclusions: Vec<Elem<Concrete>>) -> Self {
        Self {
            min,
            min_cached: None,
            max,
            max_cached: None,
            exclusions,
            flattened: None,
        }
    }

    pub fn replace_dep(
        &mut self,
        to_replace: NodeIdx,
        replacement: Elem<Concrete>,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        if let Some(ref mut flattened) = &mut self.flattened {
            flattened
                .min
                .replace_dep(to_replace, replacement.clone(), analyzer, arena);
            flattened
                .max
                .replace_dep(to_replace, replacement.clone(), analyzer, arena);
        }
        self.min
            .replace_dep(to_replace, replacement.clone(), analyzer, arena);
        self.max
            .replace_dep(to_replace, replacement, analyzer, arena);
        self.min_cached = None;
        self.max_cached = None;
    }

    pub fn is_const(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let min = self.evaled_range_min(analyzer, arena)?;
        let max = self.evaled_range_max(analyzer, arena)?;
        Ok(min.range_eq(&max, arena))
    }

    pub fn min_is_negative(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        self.min.is_negative(false, analyzer, arena)
    }

    pub fn default_bool() -> Self {
        let min = Elem::Concrete(RangeConcrete::new(Concrete::Bool(false), Loc::Implicit));
        let max = Elem::Concrete(RangeConcrete::new(Concrete::Bool(true), Loc::Implicit));
        Self::new(min, max, vec![])
    }
    pub fn from(c: Concrete) -> Option<Self> {
        match c {
            c @ Concrete::Uint(_, _)
            | c @ Concrete::Int(_, _)
            | c @ Concrete::Bool(_)
            | c @ Concrete::Address(_)
            | c @ Concrete::String(_)
            | c @ Concrete::Bytes(_, _) => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete::new(c.clone(), Loc::Implicit)),
                Elem::Concrete(RangeConcrete::new(c, Loc::Implicit)),
                vec![],
            )),
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
                let r = Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::from(b.len()))),
                    val,
                    Loc::Implicit,
                ));
                Some(SolcRange::new(r.clone(), r, vec![]))
            }
            _e => None,
        }
    }

    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Uint(*size, 0.into()),
                            Loc::Implicit,
                        )),
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Uint(*size, U256::MAX),
                            Loc::Implicit,
                        )),
                        vec![],
                    ))
                } else {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Uint(*size, 0.into()),
                            Loc::Implicit,
                        )),
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Uint(*size, U256::from(2).pow(U256::from(*size)) - 1),
                            Loc::Implicit,
                        )),
                        vec![],
                    ))
                }
            }
            Builtin::Int(size) => {
                if *size == 256 {
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Int(*size, I256::MIN),
                            Loc::Implicit,
                        )),
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Int(*size, I256::MAX),
                            Loc::Implicit,
                        )),
                        vec![],
                    ))
                } else {
                    let max: I256 =
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::from(1);
                    let min = max * I256::from(-1i32) - I256::from(1i32);
                    Some(SolcRange::new(
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Int(*size, min),
                            Loc::Implicit,
                        )),
                        Elem::Concrete(RangeConcrete::new(
                            Concrete::Int(*size, max),
                            Loc::Implicit,
                        )),
                        vec![],
                    ))
                }
            }
            Builtin::Bool => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete::new(Concrete::Bool(false), Loc::Implicit)),
                Elem::Concrete(RangeConcrete::new(Concrete::Bool(true), Loc::Implicit)),
                vec![],
            )),
            Builtin::Address | Builtin::Payable | Builtin::AddressPayable => Some(SolcRange::new(
                Elem::Concrete(RangeConcrete::new(
                    Concrete::Address(Address::from_slice(&[0x00; 20])),
                    Loc::Implicit,
                )),
                Elem::Concrete(RangeConcrete::new(
                    Concrete::Address(Address::from_slice(&[0xff; 20])),
                    Loc::Implicit,
                )),
                vec![],
            )),
            Builtin::Bytes(size) => {
                let v: Vec<_> = (0..32u8)
                    .map(|i| if i < *size { 0xff } else { 0x00 })
                    .collect();
                Some(SolcRange::new(
                    Elem::Concrete(RangeConcrete::new(
                        Concrete::Bytes(*size, H256::from_slice(&[0x00; 32])),
                        Loc::Implicit,
                    )),
                    Elem::Concrete(RangeConcrete::new(
                        Concrete::Bytes(*size, H256::from_slice(&v[..])),
                        Loc::Implicit,
                    )),
                    vec![],
                ))
            }
            Builtin::DynamicBytes
            | Builtin::String
            | Builtin::Array(_)
            | Builtin::Mapping(_, _) => Some(SolcRange::new(
                Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::zero())),
                    Default::default(),
                    Loc::Implicit,
                )),
                Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::MAX)),
                    Default::default(),
                    Loc::Implicit,
                )),
                vec![],
            )),
            Builtin::SizedArray(s, _) => Some(SolcRange::new(
                Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(*s)),
                    Default::default(),
                    Loc::Implicit,
                )),
                Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(*s)),
                    Default::default(),
                    Loc::Implicit,
                )),
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
                    - Elem::Concrete(RangeConcrete::new(U256::from(1).into(), Loc::Implicit)),
            ),
            self.exclusions,
        )
    }

    pub fn gt_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.max(
                Elem::from(other)
                    + Elem::Concrete(RangeConcrete::new(U256::from(1).into(), Loc::Implicit)),
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
            RangeOp::Div(false) => &Self::div_dyn,
            RangeOp::Div(true) => &Self::wrapping_mul_dyn,
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

    pub fn wrapping_div_dyn(self, other: ContextVarNode) -> Self {
        Self::new(
            self.min.wrapping_div(Elem::from(other)),
            self.max.wrapping_div(Elem::from(other)),
            self.exclusions,
        )
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

    pub fn into_flattened_range(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<FlattenedRange, GraphError> {
        if let Some(cached) = &self.flattened {
            return Ok(cached.clone());
        }

        let mut min = self.min.clone();
        min.arenaize(analyzer, arena)?;
        min.cache_flatten(analyzer, arena)?;
        let mut max = self.max.clone();
        max.arenaize(analyzer, arena)?;
        max.cache_flatten(analyzer, arena)?;

        self.min = min.clone();
        self.max = max.clone();

        let mut simp_min = min.simplify_minimize(analyzer, arena)?;
        simp_min.arenaize(analyzer, arena)?;
        let mut simp_max = max.simplify_maximize(analyzer, arena)?;
        simp_max.arenaize(analyzer, arena)?;

        let flat_range = FlattenedRange {
            min: simp_min,
            max: simp_max,
            exclusions: self.exclusions.clone(),
        };
        self.flattened = Some(flat_range.clone());

        Ok(flat_range)
    }
}

impl Range<Concrete> for SolcRange {
    type GraphError = GraphError;
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

    fn cache_eval(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let mut min = std::mem::take(&mut self.min);
        let mut max = std::mem::take(&mut self.max);
        min.arenaize(analyzer, arena)?;
        max.arenaize(analyzer, arena)?;
        self.min = min;
        self.max = max;
        if self.max_cached.is_none() {
            let max = self.range_max_mut();
            max.cache_maximize(analyzer, arena)?;
            let res = self.range_max().maximize(analyzer, arena)?;
            self.max_cached = Some(arena.idx_or_upsert(res, analyzer));
        }
        if self.min_cached.is_none() {
            let min = self.range_min_mut();
            min.cache_minimize(analyzer, arena)?;
            let res = self.range_min().minimize(analyzer, arena)?;
            self.min_cached = Some(arena.idx_or_upsert(res, analyzer));
        }
        Ok(())
    }

    fn evaled_range_min(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Self::ElemTy, GraphError> {
        if let Some(cached) = &self.min_cached {
            Ok(Elem::Arena(*cached).dearenaize_clone(arena))
        } else {
            self.range_min().minimize(analyzer, arena)
        }
    }

    fn evaled_range_max(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Self::ElemTy, GraphError> {
        if let Some(cached) = &self.max_cached {
            Ok(Elem::Arena(*cached).dearenaize_clone(arena))
        } else {
            self.range_max().maximize(analyzer, arena)
        }
    }

    fn simplified_range_min(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Self::ElemTy, GraphError> {
        self.range_min()
            .flatten(false, analyzer, arena)?
            .simplify_minimize(analyzer, arena)
    }
    fn simplified_range_max(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Self::ElemTy, GraphError> {
        self.range_max()
            .flatten(true, analyzer, arena)?
            .simplify_maximize(analyzer, arena)
    }

    fn range_exclusions(&self) -> Vec<Self::ElemTy> {
        self.exclusions.clone().into_iter().collect()
    }
    fn set_range_min(&mut self, new: Self::ElemTy) {
        self.min_cached = None;
        self.flattened = None;
        self.min = new;
    }
    fn set_range_max(&mut self, new: Self::ElemTy) {
        self.max_cached = None;
        self.flattened = None;
        self.max = new;
    }

    fn add_range_exclusion(&mut self, new: Elem<Concrete>) {
        if !self.exclusions.contains(&new) {
            self.exclusions.push(new);
        }
    }
    fn set_range_exclusions(&mut self, new: Vec<Elem<Concrete>>) {
        self.exclusions = new;
    }

    fn filter_min_recursion(
        &mut self,
        self_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.min
            .filter_recursion(self_idx, new_idx, analyzer, arena);
    }
    fn filter_max_recursion(
        &mut self,
        self_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.max
            .filter_recursion(self_idx, new_idx, analyzer, arena);
    }

    fn cache_flatten(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), Self::GraphError> {
        if self.flattened.is_none() {
            self.into_flattened_range(analyzer, arena)?;
        }
        Ok(())
    }
    /// Produce a flattened range or use the cached flattened range
    fn flattened_range<'a>(
        &'a mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Cow<'a, FlattenedRange>, Self::GraphError>
    where
        Self: Sized + Clone,
    {
        if self.flattened.is_none() {
            self.cache_flatten(analyzer, arena)?;
            let Some(flat) = &self.flattened else {
                unreachable!();
            };
            return Ok(Cow::Borrowed(flat));
        } else if let Some(flat) = &self.flattened {
            return Ok(Cow::Borrowed(flat));
        } else {
            unreachable!()
        }
    }

    /// Produce a flattened range or use the cached flattened range
    fn take_flattened_range(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<FlattenedRange, Self::GraphError>
    where
        Self: Sized,
    {
        let taken = std::mem::take(&mut self.flattened);
        if let Some(flat) = taken {
            Ok(flat)
        } else {
            self.cache_flatten(analyzer, arena)?;
            self.take_flattened_range(analyzer, arena)
        }
    }
}

impl RangeEval<Concrete, Elem<Concrete>> for SolcRange {
    #[tracing::instrument(level = "trace", skip_all)]
    fn sat(&self, analyzer: &impl GraphBackend, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        matches!(
            self.evaled_range_min(analyzer, arena)
                .unwrap()
                .range_ord(&self.evaled_range_max(analyzer, arena).unwrap(), arena),
            None | Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        )
    }

    fn contains(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        let min_contains = matches!(
            self.evaled_range_min(analyzer, arena)
                .unwrap()
                .range_ord(&other.evaled_range_min(analyzer, arena).unwrap(), arena),
            Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
        );

        let max_contains = matches!(
            self.evaled_range_max(analyzer, arena)
                .unwrap()
                .range_ord(&other.evaled_range_max(analyzer, arena).unwrap(), arena),
            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
        );

        min_contains && max_contains
    }

    fn contains_elem(
        &self,
        other: &Elem<Concrete>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        let min_contains = match self
            .evaled_range_min(analyzer, arena)
            .unwrap()
            .range_ord(&other.minimize(analyzer, arena).unwrap(), arena)
        {
            Some(std::cmp::Ordering::Less) => true,
            Some(std::cmp::Ordering::Equal) => return true,
            _ => false,
        };

        let max_contains = match self
            .evaled_range_max(analyzer, arena)
            .unwrap()
            .range_ord(&other.maximize(analyzer, arena).unwrap(), arena)
        {
            Some(std::cmp::Ordering::Greater) => true,
            Some(std::cmp::Ordering::Equal) => return true,
            _ => false,
        };

        min_contains && max_contains
    }

    fn overlaps(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        let lhs_min = self.evaled_range_min(analyzer, arena).unwrap();
        let rhs_max = other.evaled_range_max(analyzer, arena).unwrap();

        match lhs_min.range_ord(&rhs_max, arena) {
            Some(std::cmp::Ordering::Less) => {
                // we know our min is less than the other max
                // check that the max is greater than or eq their min
                let lhs_max = self.evaled_range_max(analyzer, arena).unwrap();
                let rhs_min = other.evaled_range_min(analyzer, arena).unwrap();
                matches!(
                    lhs_max.range_ord(&rhs_min, arena),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                )
            }
            Some(std::cmp::Ordering::Equal) => true,
            _ => false,
        }
    }
}

impl RangeEval<Concrete, Elem<Concrete>> for FlattenedRange {
    fn sat(&self, analyzer: &impl GraphBackend, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        <FlattenedRange as Into<SolcRange>>::into(self.clone()).sat(analyzer, arena)
    }
    fn unsat(&self, analyzer: &impl GraphBackend, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        !self.sat(analyzer, arena)
    }
    fn contains(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        let other = <FlattenedRange as Into<SolcRange>>::into(other.clone());
        <FlattenedRange as Into<SolcRange>>::into(self.clone()).contains(&other, analyzer, arena)
    }
    fn contains_elem(
        &self,
        other: &Elem<Concrete>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        <FlattenedRange as Into<SolcRange>>::into(self.clone())
            .contains_elem(other, analyzer, arena)
    }
    fn overlaps(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        let other = <FlattenedRange as Into<SolcRange>>::into(other.clone());
        <FlattenedRange as Into<SolcRange>>::into(self.clone()).overlaps(&other, analyzer, arena)
    }
}
