pub mod bool_range;
pub mod len_range;
pub mod num_range;
pub mod range_elem;
pub mod range_expr;

use crate::range::bool_range::BoolElem;
use crate::AnalyzerLike;
use crate::Concrete;
use crate::ContextVarNode;
use crate::NodeIdx;
pub use bool_range::BoolRange;
pub use len_range::LenRange;
pub use num_range::Range;
pub use range_elem::RangeElem;
use range_expr::*;

use crate::Builtin;
use ethers_core::types::{I256, U256};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BuiltinRange {
    Bool(BoolRange),
    Num(Range),
}

impl From<Concrete> for BuiltinRange {
    fn from(c: Concrete) -> Self {
        let elem = BuiltinElem::from(c);
        match elem {
            BuiltinElem::Bool(b) => Self::Bool(BoolRange::from(b)),
            BuiltinElem::Num(n) => Self::Num(Range::from(n)),
        }
    }
}

impl BuiltinRange {
    pub fn elem_from_dyn(
        &self,
        idx: NodeIdx,
        range_side: DynamicRangeSide,
        loc: Loc,
    ) -> BuiltinElem {
        match self {
            Self::Bool(_) => BuiltinElem::Bool(BoolElem::Dynamic(idx, range_side, loc)),
            Self::Num(_) => BuiltinElem::Num(RangeElem::Dynamic(idx, range_side, loc)),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BuiltinElem {
    Bool(BoolElem),
    Num(RangeElem),
}

impl From<Concrete> for BuiltinElem {
    fn from(c: Concrete) -> Self {
        match c {
            Concrete::Uint(_, val) => BuiltinElem::from(val),
            Concrete::Int(_, val) => BuiltinElem::from(val),
            Concrete::Bool(b) => BuiltinElem::from(b),
            _ => todo!("other concrete range types"),
        }
    }
}

impl From<RangeElem> for BuiltinElem {
    fn from(elem: RangeElem) -> Self {
        Self::Num(elem)
    }
}

impl From<BoolElem> for BuiltinElem {
    fn from(elem: BoolElem) -> Self {
        Self::Bool(elem)
    }
}

impl From<bool> for BuiltinElem {
    fn from(val: bool) -> Self {
        let elem = BoolElem::from(val);
        BuiltinElem::from(elem)
    }
}

impl From<U256> for BuiltinElem {
    fn from(val: U256) -> Self {
        let elem = RangeElem::from(val);
        BuiltinElem::from(elem)
    }
}

impl From<I256> for BuiltinElem {
    fn from(val: I256) -> Self {
        let elem = RangeElem::from(val);
        BuiltinElem::from(elem)
    }
}

impl BuiltinElem {
    pub fn num_elem(self) -> RangeElem {
        match self {
            Self::Num(re) => re,
            _ => panic!("Not a numeric range"),
        }
    }

    pub fn bool_elem(self) -> BoolElem {
        match self {
            Self::Bool(b) => b,
            _ => panic!("Not a boolean range"),
        }
    }
}

pub trait RangeSize {
    type Output;
    fn range_min(&self) -> Self::Output;
    fn range_max(&self) -> Self::Output;
    fn set_range_min(&mut self, new: Self::Output);
    fn set_range_max(&mut self, new: Self::Output);
}

pub trait ToRangeString {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString;
    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString;
    fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString>;
}

pub trait ElemEval {
    fn eval(&self, analyzer: &impl AnalyzerLike) -> Self;
    fn range_eq(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool;
    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering>;
}

pub trait RangeEval<T: ElemEval>: RangeSize<Output = T> {
    fn sat(&self, analyzer: &impl AnalyzerLike) -> bool {
        match self
            .range_min()
            .eval(analyzer)
            .range_ord(&self.range_max().eval(analyzer))
        {
            None | Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal) => true,
            _ => false,
        }
    }
    fn unsat(&self, analyzer: &impl AnalyzerLike) -> bool {
        !self.sat(analyzer)
    }
}

impl<R, T> RangeEval<T> for R
where
    R: RangeSize<Output = T>,
    T: ElemEval + std::fmt::Debug,
{
}

impl RangeSize for BuiltinRange {
    type Output = BuiltinElem;
    fn range_min(&self) -> BuiltinElem {
        match self {
            BuiltinRange::Bool(b_range) => BuiltinElem::Bool(b_range.range_min()),
            BuiltinRange::Num(num_range) => BuiltinElem::Num(num_range.range_min()),
        }
    }

    fn range_max(&self) -> BuiltinElem {
        match self {
            BuiltinRange::Bool(b_range) => BuiltinElem::Bool(b_range.range_max()),
            BuiltinRange::Num(num_range) => BuiltinElem::Num(num_range.range_max()),
        }
    }

    fn set_range_min(&mut self, new: Self::Output) {
        match (self, new) {
            (BuiltinRange::Bool(b_range), BuiltinElem::Bool(new)) => b_range.set_range_min(new),
            (BuiltinRange::Num(num_range), BuiltinElem::Num(new)) => num_range.set_range_min(new),
            (_, _) => panic!("Mismatched range elem and range type"),
        }
    }

    fn set_range_max(&mut self, new: Self::Output) {
        match (self, new) {
            (BuiltinRange::Bool(b_range), BuiltinElem::Bool(new)) => b_range.set_range_max(new),
            (BuiltinRange::Num(num_range), BuiltinElem::Num(new)) => num_range.set_range_max(new),
            (_, _) => panic!("Mismatched range elem and range type"),
        }
    }
}

impl ElemEval for BuiltinElem {
    fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
        match self {
            Self::Bool(b) => BuiltinElem::Bool(b.eval(analyzer)),
            Self::Num(num) => BuiltinElem::Num(num.eval(analyzer)),
        }
    }
    fn range_eq(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        match (self, other) {
            (BuiltinElem::Bool(b0), BuiltinElem::Bool(b1)) => b0.range_eq(b1, analyzer),
            (BuiltinElem::Num(n0), BuiltinElem::Num(n1)) => n0.range_eq(n1, analyzer),
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (BuiltinElem::Bool(b0), BuiltinElem::Bool(b1)) => b0.range_ord(b1),
            (BuiltinElem::Num(n0), BuiltinElem::Num(n1)) => n0.range_ord(n1),
            _ => None,
        }
    }
}

impl ToRangeString for BuiltinElem {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
            BuiltinElem::Bool(b) => b.def_string(analyzer),
            BuiltinElem::Num(b) => b.def_string(analyzer),
        }
    }
    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
            BuiltinElem::Bool(b) => b.to_range_string(analyzer),
            BuiltinElem::Num(b) => b.to_range_string(analyzer),
        }
    }
    fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        match self {
            BuiltinElem::Bool(b) => b.bounds_range_string(analyzer),
            BuiltinElem::Num(b) => b.bounds_range_string(analyzer),
        }
    }
}

impl BuiltinRange {
    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(BuiltinRange::Num(Range {
                        min: RangeElem::Concrete(0.into(), Loc::Implicit),
                        max: RangeElem::Concrete(U256::MAX, Loc::Implicit),
                    }))
                } else {
                    Some(BuiltinRange::Num(Range {
                        min: RangeElem::Concrete(0.into(), Loc::Implicit),
                        max: RangeElem::Concrete(
                            U256::from(2).pow(U256::from(*size)) - 1,
                            Loc::Implicit,
                        ),
                    }))
                }
            }
            Builtin::Int(size) => {
                if *size == 256 {
                    Some(BuiltinRange::Num(Range {
                        min: RangeElem::SignedConcrete(I256::MIN, Loc::Implicit),
                        max: RangeElem::SignedConcrete(I256::MAX, Loc::Implicit),
                    }))
                } else {
                    let max: I256 =
                        I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - 1.into();
                    let min = max * I256::from(-1i32);
                    Some(BuiltinRange::Num(Range {
                        min: RangeElem::SignedConcrete(min, Loc::Implicit),
                        max: RangeElem::SignedConcrete(max, Loc::Implicit),
                    }))
                }
            }
            Builtin::Bool => Some(BuiltinRange::Bool(BoolRange::default())),
            _ => None,
        }
    }

    pub fn as_num_range(self) -> Range {
        match self {
            BuiltinRange::Num(range) => range,
            _ => panic!("wasn't num range"),
        }
    }

    pub fn num_range(&self) -> &Range {
        match self {
            BuiltinRange::Num(range) => range,
            _ => panic!("wasn't num range"),
        }
    }

    pub fn bool_range(&self) -> &BoolRange {
        match self {
            BuiltinRange::Bool(b_range) => b_range,
            _ => panic!("wasn't num range"),
        }
    }

    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        self.num_range().dependent_on()
    }

    pub fn lte(self, other: Self) -> Self {
        Self::Num(self.as_num_range().lte(other.as_num_range()))
    }

    pub fn gte(self, other: Self) -> Self {
        Self::Num(self.as_num_range().gte(other.as_num_range()))
    }

    pub fn lt(self, other: Self) -> Self {
        Self::Num(self.as_num_range().lt(other.as_num_range()))
    }

    pub fn gt(self, other: Self) -> Self {
        Self::Num(self.as_num_range().gt(other.as_num_range()))
    }

    pub fn fn_from_op(op: Op) -> impl Fn(Self, Self) -> Self {
        match op {
            Op::Add => Self::add,
            Op::Sub => Self::sub,
            Op::Mul => Self::mul,
            Op::Div => Self::div,
            Op::Mod => Self::r#mod,
            Op::Min => Self::min,
            Op::Max => Self::max,
            _ => unreachable!("Comparator operations shouldn't exist in a range"),
        }
    }

    pub fn dyn_fn_from_op(
        op: Op,
    ) -> (
        &'static dyn Fn(Self, ContextVarNode, (DynamicRangeSide, DynamicRangeSide), Loc) -> Self,
        (DynamicRangeSide, DynamicRangeSide),
    ) {
        match op {
            Op::Add => (
                &Self::add_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
            ),
            Op::Sub => (
                &Self::sub_dyn,
                (DynamicRangeSide::Max, DynamicRangeSide::Min),
            ),
            Op::Mul => (
                &Self::mul_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
            ),
            Op::Div => (
                &Self::div_dyn,
                (DynamicRangeSide::Max, DynamicRangeSide::Min),
            ),
            Op::Mod => (
                &Self::mod_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
            ),
            Op::Min => (
                &Self::min_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
            ),
            Op::Max => (
                &Self::max_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
            ),
            _ => unreachable!("Comparator operations shouldn't exist in a range"),
        }
    }

    pub fn add(self, other: Self) -> Self {
        Self::Num(self.as_num_range().add(other.as_num_range()))
    }

    pub fn add_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().add_dyn(other, range_sides, loc))
    }

    pub fn sub(self, other: Self) -> Self {
        Self::Num(self.as_num_range().sub(other.as_num_range()))
    }

    pub fn sub_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().sub_dyn(other, range_sides, loc))
    }

    pub fn mul(self, other: Self) -> Self {
        Self::Num(self.as_num_range().mul(other.as_num_range()))
    }

    pub fn mul_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().mul_dyn(other, range_sides, loc))
    }

    pub fn div(self, other: Self) -> Self {
        Self::Num(self.as_num_range().div(other.as_num_range()))
    }

    pub fn div_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().div_dyn(other, range_sides, loc))
    }

    pub fn r#mod(self, other: Self) -> Self {
        Self::Num(self.as_num_range().r#mod(other.as_num_range()))
    }

    pub fn mod_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().mod_dyn(other, range_sides, loc))
    }

    pub fn min(self, other: Self) -> Self {
        Self::Num(self.as_num_range().min(other.as_num_range()))
    }

    pub fn min_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().min_dyn(other, range_sides, loc))
    }

    pub fn max(self, other: Self) -> Self {
        Self::Num(self.as_num_range().max(other.as_num_range()))
    }

    pub fn max_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self::Num(self.as_num_range().max_dyn(other, range_sides, loc))
    }
}

impl From<U256> for BuiltinRange {
    fn from(val: U256) -> Self {
        BuiltinRange::Num(Range::from(val))
    }
}

impl From<I256> for BuiltinRange {
    fn from(val: I256) -> Self {
        BuiltinRange::Num(Range::from(val))
    }
}

impl From<bool> for BuiltinRange {
    fn from(val: bool) -> Self {
        BuiltinRange::Bool(BoolRange::from(val))
    }
}

use solang_parser::pt::Loc;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DynamicRangeSide {
    Min,
    Max,
}

impl ToString for DynamicRangeSide {
    fn to_string(&self) -> String {
        match self {
            Self::Min => "range_min".to_string(),
            Self::Max => "range_max".to_string(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeElemString {
    pub s: String,
    pub loc: Loc,
}

impl RangeElemString {
    pub fn new(s: String, loc: Loc) -> Self {
        Self { s, loc }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeString {
    pub min: RangeElemString,
    pub max: RangeElemString,
}

impl RangeString {
    pub fn new(min: RangeElemString, max: RangeElemString) -> Self {
        Self { min, max }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Op {
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Min,
    Max,
    Lt,
    Lte,
    Gt,
    Gte,
    Eq,
    Not,
}

impl Op {
    pub fn inverse(self) -> Self {
        use Op::*;
        match self {
            Add => Sub,
            Mul => Div,
            Sub => Add,
            Div => Mul,
            e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }
}

impl ToString for Op {
    fn to_string(&self) -> String {
        use Op::*;
        match self {
            Add => "+".to_string(),
            Mul => "*".to_string(),
            Sub => "-".to_string(),
            Div => "/".to_string(),
            Mod => "%".to_string(),
            Min => "min".to_string(),
            Max => "max".to_string(),
            Lt => "<".to_string(),
            Gt => ">".to_string(),
            Lte => "<=".to_string(),
            Gte => ">=".to_string(),
            Eq => "==".to_string(),
            Not => "!".to_string(),
        }
    }
}
