use crate::ContextNode;
use crate::range::Op;
use crate::range::DynamicRangeSide;
use crate::range::ElemEval;
use crate::range::RangeElemString;
use crate::range::RangeSize;
use crate::range::RangeString;
use crate::range::ToRangeString;
use crate::AnalyzerLike;
use crate::ContextVarNode;
use crate::NodeIdx;
use crate::VarType;
use solang_parser::pt::Loc;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct BoolRange {
    pub min: BoolElem,
    pub max: BoolElem,
}

impl BoolRange {
    pub fn eq(self, other: Self) -> Self {
        Self {
            min: self.min.eq(other.min),
            max: self.max.eq(other.max),
        }
    }

    pub fn eq_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .eq(BoolElem::Dynamic(other.into(), range_sides.0, loc)),
            max: self
                .max
                .eq(BoolElem::Dynamic(other.into(), range_sides.1, loc)),
        }
    }

    pub fn neq(self, other: Self) -> Self {
        Self {
            min: self.min.neq(other.min),
            max: self.max.neq(other.max),
        }
    }

    pub fn neq_dyn(
        self,
        other: ContextVarNode,
        range_sides: (DynamicRangeSide, DynamicRangeSide),
        loc: Loc,
    ) -> Self {
        Self {
            min: self
                .min
                .neq(BoolElem::Dynamic(other.into(), range_sides.0, loc)),
            max: self
                .max
                .neq(BoolElem::Dynamic(other.into(), range_sides.1, loc)),
        }
    }
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
        Self { min: b.clone(), max: b }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum BoolElem {
    True(Loc),
    False(Loc),
    Dynamic(NodeIdx, DynamicRangeSide, Loc),
    Expr(Box<Self>, Op, Box<Self>),
}

impl BoolElem {
    pub fn set_loc(&mut self, loc: Loc) {
        use BoolElem::*;
        match self {
            True(ref mut curr_loc) | False(ref mut curr_loc) | Dynamic(_, _, ref mut curr_loc) => {
                *curr_loc = loc
            }
            &mut BoolElem::Expr(_, _, _) => todo!()
        }
    }

    pub fn invert(self, new_loc: Loc) -> Option<Self> {
        use BoolElem::*;
        match self {
            True(_) => Some(False(new_loc)),
            False(_) => Some(True(new_loc)),
            _ => None,
        }
    }

    pub fn exec_op(&self, other: &Self, op: Op, ctx: ContextNode, analyzer: &impl AnalyzerLike) -> Option<BoolElem> {
        match op {
            Op::Eq => {
                match (self.eval(ctx, analyzer), other.eval(ctx, analyzer)) {
                    (BoolElem::True(_), BoolElem::True(_)) => Some(true.into()),
                    (BoolElem::False(_), BoolElem::False(_)) => Some(true.into()),
                    _ => Some(false.into())
                }
            }
            Op::Neq => {
                match (self.eval(ctx, analyzer), other.eval(ctx, analyzer)) {
                    (BoolElem::True(_), BoolElem::False(_)) => Some(true.into()),
                    (BoolElem::False(_), BoolElem::True(_)) => Some(true.into()),
                    _ => Some(false.into())
                }
            }
            _ => None
        }
    }

    pub fn eq(self, other: Self) -> Self {
        Self::Expr(Box::new(self), Op::Eq, Box::new(other))
    }

    pub fn neq(self, other: Self) -> Self {
        Self::Expr(Box::new(self), Op::Neq, Box::new(other))
    }
}

impl ElemEval for BoolElem {
    fn eval(&self, ctx: ContextNode, analyzer: &impl AnalyzerLike) -> Self {
        use BoolElem::*;
        match self {
            Dynamic(idx, range_side, _) => {
                let cvar = ContextVarNode::from(*idx).underlying(analyzer);
                match &cvar.ty {
                    VarType::BuiltIn(_, maybe_range) => {
                        if let Some(range) = maybe_range {
                            match range_side {
                                DynamicRangeSide::Min => Self::from(
                                    range.bool_range().range_min().clone().eval(ctx, analyzer),
                                ),
                                DynamicRangeSide::Max => Self::from(
                                    range.bool_range().range_max().clone().eval(ctx, analyzer),
                                ),
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
            Expr(lhs, op, rhs) => if let Some(elem) = lhs.exec_op(&rhs, *op, ctx, analyzer) { elem } else { self.clone() },
            _ => self.clone(),
        }
    }

    fn range_eq(&self, other: &Self, ctx: ContextNode, analyzer: &impl AnalyzerLike) -> bool {
        use BoolElem::*;
        match (self.eval(ctx, analyzer), other.eval(ctx, analyzer)) {
            (True(_), True(_)) => true,
            (False(_), False(_)) => true,
            (Dynamic(idx0, side0, _), Dynamic(idx1, side1, _)) => idx0 == idx1 && side0 == side1,
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use BoolElem::*;
        match (self, other) {
            (True(_), True(_)) => Some(std::cmp::Ordering::Equal),
            (False(_), False(_)) => Some(std::cmp::Ordering::Equal),
            (True(_), False(_)) => Some(std::cmp::Ordering::Greater),
            (False(_), True(_)) => Some(std::cmp::Ordering::Less),
            _ => None,
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
        self.min.clone()
    }

    fn range_max(&self) -> BoolElem {
        self.max.clone()
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
            Expr(lhs, _, _) => lhs.def_string(analyzer),
        }
    }
    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use BoolElem::*;
        match self {
            True(loc) => RangeElemString::new(true.to_string(), *loc),
            False(loc) => RangeElemString::new(false.to_string(), *loc),
            Dynamic(idx, _range_side, loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = format!(
                    "{}",
                    as_var.display_name(analyzer),
                );
                RangeElemString::new(name, *loc)
            }
            Expr(lhs, op, rhs) => RangeElemString::new(format!("{} {} {}", lhs.to_range_string(analyzer).s, op.to_string(), rhs.to_range_string(analyzer).s), Loc::Implicit),
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
