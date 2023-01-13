use crate::range::RangeString;
use crate::ContextVarNode;
use crate::range::RangeElemString;
use crate::range::ToRangeString;
use crate::range::DynamicRangeSide;
use crate::NodeIdx;
use solang_parser::pt::Loc;
use crate::range::ElemEval;
use crate::AnalyzerLike;
use crate::VarType;
use crate::range::RangeSize;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BoolRange {
    pub min: BoolElem,
    pub max: BoolElem,
}

impl Default for BoolRange {
    fn default() -> Self {
        Self {
            min: BoolElem::False(Loc::Implicit),
            max: BoolElem::True(Loc::Implicit),
        }
    }
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
    Dynamic(NodeIdx, DynamicRangeSide, Loc)
}

impl BoolElem {
    pub fn set_loc(&mut self, loc: Loc) {
        use BoolElem::*;
        match self {
            True(ref mut curr_loc)
            | False(ref mut curr_loc)
            | Dynamic(_, _, ref mut curr_loc) => *curr_loc = loc,
        }
    }

    pub fn invert(self, new_loc: Loc) -> Option<Self> {
        use BoolElem::*;
        match self {
            True(_) => Some(False(new_loc)),
            False(_) => Some(True(new_loc)),
            _ => None
        }
    }
}

impl ElemEval for BoolElem {
    fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
        use BoolElem::*;
        match self {
            Dynamic(idx, range_side, _) => {
                let cvar = ContextVarNode::from(*idx).underlying(analyzer);
                match &cvar.ty {
                    VarType::BuiltIn(_, maybe_range) => {
                        if let Some(range) = maybe_range {
                            match range_side {
                                DynamicRangeSide::Min => {
                                    Self::from(range.bool_range().range_min().clone().eval(analyzer))
                                }
                                DynamicRangeSide::Max => {
                                    Self::from(range.bool_range().range_max().clone().eval(analyzer))
                                }
                            }
                        } else {
                            self.clone()
                        }
                    }
                    VarType::Concrete(concrete_node) => match concrete_node.underlying(analyzer) {
                        crate::Concrete::Bool(b) => {
                            let mut bre = BoolElem::from(*b);
                            bre.set_loc(cvar.loc.unwrap_or(Loc::Implicit));
                            bre
                        }
                        _ => self.clone(),
                    },
                    _ => self.clone(),
                }
            }
            _ => self.clone()
        }
    }

    fn range_eq(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        use BoolElem::*;
        match (self.eval(analyzer), other.eval(analyzer)) {
            (True(_), True(_)) => true,
            (False(_), False(_)) => true,
            (Dynamic(idx0, side0, _), Dynamic(idx1, side1, _)) => idx0 == idx1 && side0 == side1,
            _ => false
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use BoolElem::*;
        match (self, other) {
            (True(_), True(_)) => Some(std::cmp::Ordering::Equal),
            (False(_), False(_)) => Some(std::cmp::Ordering::Equal),
            (True(_), False(_)) => Some(std::cmp::Ordering::Greater),
            (False(_), True(_)) => Some(std::cmp::Ordering::Less),
            _ => None
        }
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