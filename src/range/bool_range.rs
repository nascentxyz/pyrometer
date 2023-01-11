use crate::range::RangeString;
use crate::ContextVarNode;
use crate::range::RangeElemString;
use crate::range::ToRangeString;
use crate::range::DynamicRangeSide;
use crate::NodeIdx;
use solang_parser::pt::Loc;
use crate::range::ElemEval;
use crate::AnalyzerLike;
use crate::range::RangeSize;

#[derive(Default, Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BoolRange {
    pub min: BoolElem,
    pub max: BoolElem,
}

impl From<bool> for BoolRange {
    fn from(b: bool) -> Self {
        Self {
            min: b.into(),
            max: b.into(),
        }
    }
}

impl From<BoolElem> for BoolRange {
    fn from(b: BoolElem) -> Self {
        Self {
            min: b,
            max: b,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BoolElem {
    True(Loc),
    False(Loc),
    Either(Loc),
    Dynamic(NodeIdx, DynamicRangeSide, Loc)
}

impl Default for BoolElem {
    fn default() -> Self {
        BoolElem::Either(Loc::Implicit)
    }
}

impl ElemEval for BoolElem {
    fn eval(&self, _analyzer: &impl AnalyzerLike) -> Self {
        *self
    }
}

impl From<bool> for BoolElem {
    fn from(b: bool) -> Self {
        if b {
            Self::True(Loc::Implicit)
        } else {
            Self::False(Loc::Implicit)
        }
    }
}

impl RangeSize for BoolRange {
    type Output = BoolElem;
    fn range_min(&self) -> BoolElem {
        self.min
    }

    fn range_max(&self) -> BoolElem {
        self.max
    }

    fn set_range_min(&mut self, new: Self::Output) {
        self.min = new;
    }

    fn set_range_max(&mut self, new: Self::Output) {
        self.max = new;
    }
}

impl ToRangeString for BoolElem {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use BoolElem::*;
        match self {
            True(loc) => RangeElemString::new(true.to_string(), *loc),
            False(loc) => RangeElemString::new(false.to_string(), *loc),
            Either(loc) => RangeElemString::new("(true || false)".to_string(), *loc),
            Dynamic(idx, _range_side, _loc) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer);
                RangeElemString::new(cvar.display_name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
        }
    }
    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use BoolElem::*;
        match self {
            True(loc) => RangeElemString::new(true.to_string(), *loc),
            False(loc) => RangeElemString::new(false.to_string(), *loc),
            Either(loc) => RangeElemString::new("(true || false)".to_string(), *loc),
            Dynamic(idx, range_side, loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = format!(
                    "{}.{}",
                    as_var.display_name(analyzer),
                    range_side.to_string()
                );
                RangeElemString::new(name, *loc)
            }
        }

    }
    fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use BoolElem::*;
        let mut range_strings = vec![];
        match self {
            Dynamic(idx, _range_side, _loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.display_name(analyzer);
                if let Some(range) = as_var.range(analyzer) {
                    let mut min = range.range_min().to_range_string(analyzer);
                    min.s = format!("\"{}\" ∈ {{{}, ", name, min.s);
                    let max = range.range_max().to_range_string(analyzer);

                    range_strings.push(RangeString::new(min, max));

                    range_strings.extend(range.range_min().bounds_range_string(analyzer));
                    range_strings.extend(range.range_max().bounds_range_string(analyzer));
                }
            }
            _ => {}
        }

        range_strings

    }
}