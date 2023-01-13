use crate::range::RangeSize;
use crate::{
    range::{DynamicRangeSide, Op, RangeElem},
    ContextVarNode,
};
use ethers_core::types::I256;
use ethers_core::types::U256;
use solang_parser::pt::Loc;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Range {
    pub min: RangeElem,
    pub max: RangeElem,
}

impl RangeSize for Range {
    type Output = RangeElem;
    fn range_min(&self) -> RangeElem {
        self.min.clone()
    }
    fn range_max(&self) -> RangeElem {
        self.max.clone()
    }

    fn set_range_min(&mut self, new: Self::Output) {
        self.min = new;
    }

    fn set_range_max(&mut self, new: Self::Output) {
        self.max = new;
    }
}

impl From<U256> for Range {
    fn from(val: U256) -> Self {
        let elem = RangeElem::from(val);
        Range::from(elem)
    }
}

impl From<I256> for Range {
    fn from(val: I256) -> Self {
        let elem = RangeElem::from(val);
        Range::from(elem)
    }
}

impl From<RangeElem> for Range {
    fn from(elem: RangeElem) -> Self {
        Range {
            min: elem.clone(),
            max: elem,
        }
    }
}

impl Range {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.min.dependent_on();
        deps.extend(self.max.dependent_on());
        deps
    }

    pub fn lte(self, other: Self) -> Self {
        Self {
            min: self.min,
            max: self.max.min(other.max),
        }
    }

    pub fn gte(self, other: Self) -> Self {
        Self {
            min: self.min.max(other.min),
            max: self.max,
        }
    }

    pub fn lt(self, other: Self) -> Self {
        Self {
            min: self.min,
            max: self
                .max
                .min(other.max - RangeElem::Concrete(1.into(), Loc::Implicit)),
        }
    }

    pub fn gt(self, other: Self) -> Self {
        Self {
            min: self
                .min
                .max(other.min + RangeElem::Concrete(1.into(), Loc::Implicit)),
            max: self.max,
        }
    }

    pub fn fn_from_op(op: Op) -> impl Fn(Range, Range) -> Range {
        match op {
            Op::Add => Self::add,
            Op::Sub => Self::sub,
            Op::Mul => Self::mul,
            Op::Div => Self::div,
            Op::Shl => Self::shl,
            Op::Shr => Self::shr,
            Op::Mod => Self::r#mod,
            Op::Min => Self::min,
            Op::Max => Self::max,
            _ => unreachable!("Comparator operations shouldn't exist in a range"),
        }
    }

    pub fn dyn_fn_from_op(
        op: Op,
    ) -> (
        &'static dyn Fn(Range, ContextVarNode, (DynamicRangeSide, DynamicRangeSide), Loc) -> Range,
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
            Op::Shr => (
                &Self::shr_dyn,
                (DynamicRangeSide::Max, DynamicRangeSide::Min),
            ),
            Op::Shl => (
                &Self::shl_dyn,
                (DynamicRangeSide::Min, DynamicRangeSide::Max),
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
        Self {
            min: self.min + other.min,
            max: self.max + other.max,
        }
    }

    pub fn add_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min + RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max + RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn sub(self, other: Self) -> Self {
        Self {
            min: self.min - other.max,
            max: self.max - other.min,
        }
    }

    pub fn sub_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min - RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max - RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn mul(self, other: Self) -> Self {
        Self {
            min: self.min * other.min,
            max: self.max * other.max,
        }
    }

    pub fn mul_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min * RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max * RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn div(self, other: Self) -> Self {
        Self {
            min: self.min / other.max,
            max: self.max / other.min,
        }
    }

    pub fn div_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min / RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max / RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn shl(self, other: Self) -> Self {
        Self {
            min: self.min << other.min,
            max: self.max << other.max,
        }
    }

    pub fn shl_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min << RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max << RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn shr(self, other: Self) -> Self {
        Self {
            min: self.min >> other.min,
            max: self.max >> other.max,
        }
    }

    pub fn shr_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min >> RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max >> RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn r#mod(self, other: Self) -> Self {
        Self {
            min: self.min % other.min,
            max: self.max % other.max,
        }
    }

    pub fn mod_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self.min % RangeElem::Dynamic(other.into(), range_sides.0, loc),
            max: self.max % RangeElem::Dynamic(other.into(), range_sides.1, loc),
        }
    }

    pub fn min(self, other: Self) -> Self {
        Self {
            min: self.min.min(other.min),
            max: self.max.min(other.max),
        }
    }

    pub fn min_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .min(RangeElem::Dynamic(other.into(), range_sides.0, loc)),
            max: self
                .max
                .min(RangeElem::Dynamic(other.into(), range_sides.1, loc)),
        }
    }

    pub fn max(self, other: Self) -> Self {
        Self {
            min: self.min.max(other.min),
            max: self.max.max(other.max),
        }
    }

    pub fn max_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .max(RangeElem::Dynamic(other.into(), range_sides.0, loc)),
            max: self
                .max
                .max(RangeElem::Dynamic(other.into(), range_sides.1, loc)),
        }
    }
}
