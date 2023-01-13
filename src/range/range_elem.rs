use crate::range::ElemEval;
use crate::range::RangeSize;
use crate::range::ToRangeString;
use crate::{
    range::{DynamicRangeSide, Op, RangeElemString, RangeExpr, RangeExprElem, RangeString},
    AnalyzerLike, ContextVarNode, NodeIdx, VarType,
};
use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;

use std::ops::{Add, Div, Mul, Rem, Sub, Shl, Shr};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeElem {
    // TODO: add max or size to this element to do proper bounds (except unchecked)
    Concrete(U256, Loc),
    SignedConcrete(I256, Loc),
    Dynamic(NodeIdx, DynamicRangeSide, Loc),
    Complex(RangeExpr),
}

impl From<U256> for RangeElem {
    fn from(val: U256) -> Self {
        Self::Concrete(val, Loc::Implicit)
    }
}

impl From<I256> for RangeElem {
    fn from(val: I256) -> Self {
        Self::SignedConcrete(val, Loc::Implicit)
    }
}

impl RangeElem {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Dynamic(idx, ..) => vec![ContextVarNode::from(*idx)],
            Self::Complex(expr) => expr.dependent_on(),
            _ => vec![],
        }
    }

    pub fn min(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Min,
            rhs: RangeExprElem::from(other),
        };
        RangeElem::Complex(expr)
    }

    pub fn max(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Max,
            rhs: RangeExprElem::from(other),
        };
        RangeElem::Complex(expr)
    }
}

impl Add for RangeElem {
    type Output = Self;

    fn add(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Add,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Sub for RangeElem {
    type Output = Self;

    fn sub(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Sub,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Mul for RangeElem {
    type Output = Self;

    fn mul(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Mul,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Div for RangeElem {
    type Output = Self;

    fn div(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Div,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Shl for RangeElem {
    type Output = Self;

    fn shl(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Shl,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Shr for RangeElem {
    type Output = Self;

    fn shr(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Shr,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl Rem for RangeElem {
    type Output = Self;

    fn rem(self, other: RangeElem) -> Self {
        let expr = RangeExpr {
            lhs: RangeExprElem::from(self),
            op: Op::Mod,
            rhs: RangeExprElem::from(other),
        };
        Self::Complex(expr)
    }
}

impl ElemEval for RangeElem {
    fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
        use RangeElem::*;
        match self {
            Concrete(..) => self.clone(),
            SignedConcrete(..) => self.clone(),
            Dynamic(idx, range_side, _) => {
                let cvar = ContextVarNode::from(*idx).underlying(analyzer);
                match &cvar.ty {
                    VarType::BuiltIn(_, maybe_range) => {
                        if let Some(range) = maybe_range {
                            match range_side {
                                DynamicRangeSide::Min => {
                                    Self::from(range.num_range().range_min().clone().eval(analyzer))
                                }
                                DynamicRangeSide::Max => {
                                    Self::from(range.num_range().range_max().clone().eval(analyzer))
                                }
                            }
                        } else {
                            self.clone()
                        }
                    }
                    VarType::Concrete(concrete_node) => match concrete_node.underlying(analyzer) {
                        crate::Concrete::Uint(_, val) => {
                            Self::Concrete(*val, cvar.loc.unwrap_or(Loc::Implicit))
                        }
                        crate::Concrete::Int(_, val) => {
                            Self::SignedConcrete(*val, cvar.loc.unwrap_or(Loc::Implicit))
                        }
                        _ => self.clone(),
                    },
                    _ => self.clone(),
                }
            }
            Complex(ref expr) => {
                if let Some(elem) = expr.eval(analyzer) {
                    elem
                } else {
                    self.clone()
                }
            }
        }
    }

    fn range_eq(&self, other: &Self, analyzer: &impl AnalyzerLike) -> bool {
        use RangeElem::*;
        match (self.eval(analyzer), other.eval(analyzer)) {
            (Concrete(val0, _), Concrete(val1, _)) => val0 == val1,
            (SignedConcrete(val0, _), SignedConcrete(val1, _)) => val0 == val1,
            (Concrete(val0, _), SignedConcrete(val1, _)) => {
                if val1 >= I256::from(0) {
                    val0 == val1.into_raw()
                } else {
                    false
                }
            }
            (SignedConcrete(val0, _), Concrete(val1, _)) => {
                if val0 >= I256::from(0) {
                    val0.into_raw() == val1
                } else {
                    false
                }
            }
            (Dynamic(node0, side0, _), Dynamic(node1, side1, _)) => {
                node0 == node1 && side0 == side1
            }
            (Complex(expr0), Complex(expr1)) => expr0.range_eq(&expr1, analyzer),
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use RangeElem::*;
        match (self, other) {
            (Concrete(s, _), Concrete(o, _)) => Some(s.cmp(o)),
            (SignedConcrete(s, _), SignedConcrete(o, _)) => Some(s.cmp(o)),
            (SignedConcrete(s, _), Concrete(o, _)) => {
                if s >= &I256::from(0) {
                    Some(s.into_raw().cmp(o))
                } else {
                    Some(std::cmp::Ordering::Less)
                }
            }
            (Concrete(s, _), SignedConcrete(o, _)) => {
                if o >= &I256::from(0) {
                    Some(s.cmp(&o.into_raw()))
                } else {
                    Some(std::cmp::Ordering::Greater)
                }
            }
            _ => None,
        }
    }
}

impl ToRangeString for RangeElem {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeElem::*;
        match self {
            Complex(expr) => expr.def_string(analyzer),
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, _range_side, _loc) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer);
                RangeElemString::new(cvar.display_name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
        }
    }

    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeElem::*;
        match self {
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, range_side, loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = format!(
                    "{}.{}",
                    as_var.display_name(analyzer),
                    range_side.to_string()
                );
                RangeElemString::new(name, *loc)
            }
            Complex(expr) => expr.to_range_string(analyzer),
        }
    }

    fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeElem::*;
        let mut range_strings = vec![];
        match self {
            Dynamic(idx, _range_side, _loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.display_name(analyzer);
                if let Some(range) = as_var.range(analyzer) {
                    if let Some(ord) = range
                        .num_range()
                        .range_min()
                        .range_ord(&range.num_range().range_max())
                    {
                        match ord {
                            std::cmp::Ordering::Greater => {
                                let mut min = range.range_min().to_range_string(analyzer);
                                let max = range.range_max().to_range_string(analyzer);
                                min.s = format!("Always will revert, minimum bound for \"{}\" ({}) is required to be greater than max ({})", name, min.s, max.s);
                                range_strings.push(RangeString::new(min, max));
                                return range_strings;
                            }
                            _ => {}
                        }
                    }

                    let mut min = range.range_min().to_range_string(analyzer);
                    min.s = format!("\"{}\" ∈ {{{}, ", name, min.s);
                    let max = range.range_max().to_range_string(analyzer);

                    range_strings.push(RangeString::new(min, max));

                    range_strings.extend(range.range_min().bounds_range_string(analyzer));
                    range_strings.extend(range.range_max().bounds_range_string(analyzer));
                }
            }
            Complex(expr) => range_strings.extend(expr.bounds_range_string(analyzer)),
            _ => {}
        }

        range_strings
    }
}
