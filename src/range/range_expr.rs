use crate::range::RangeSize;
use crate::range::ToRangeString;
use crate::range::ElemEval;
use crate::{
    range::{DynamicRangeSide, Op, RangeElem, RangeElemString, RangeString},
    AnalyzerLike, ContextVarNode, NodeIdx, VarType,
};
use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;
use std::convert::TryFrom;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeExprElem {
    Expr(Box<RangeExpr>),
    Concrete(U256, Loc),
    SignedConcrete(I256, Loc),
    Dynamic(NodeIdx, DynamicRangeSide, Loc),
}

impl From<RangeElem> for RangeExprElem {
    fn from(elem: RangeElem) -> Self {
        match elem {
            RangeElem::Complex(expr) => Self::Expr(Box::new(expr)),
            RangeElem::Concrete(val, loc) => Self::Concrete(val, loc),
            RangeElem::SignedConcrete(val, loc) => Self::SignedConcrete(val, loc),
            RangeElem::Dynamic(idx, range_side, loc) => Self::Dynamic(idx, range_side, loc),
        }
    }
}

impl ElemEval for RangeExprElem {
    fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
        use RangeExprElem::*;
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
            Expr(ref expr) => {
                if let Some(elem) = expr.eval(analyzer) {
                    Self::from(elem)
                } else {
                    self.clone()
                }
            }
        }
    }
}

impl ToRangeString for RangeExprElem {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeExprElem::*;
        match self {
            Expr(expr) => expr.def_string(analyzer),
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
        use RangeExprElem::*;
        match self {
            Expr(expr) => expr.to_range_string(analyzer),
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
        }
    }

    fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeExprElem::*;
        match self {
            Dynamic(idx, range_side, loc) => {
                RangeElem::Dynamic(*idx, *range_side, *loc).bounds_range_string(analyzer)
            }
            Expr(expr) => expr.bounds_range_string(analyzer),
            _ => vec![],
        }
    }
}

impl RangeExprElem {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Dynamic(idx, ..) => vec![ContextVarNode::from(*idx)],
            Self::Expr(expr) => expr.dependent_on(),
            _ => vec![],
        }
    }

    pub fn exec_op(&self, other: &Self, op: Op) -> Option<RangeElem> {
        match (self, other) {
            (Self::Concrete(self_val, loc), Self::Concrete(other_val, _)) => match op {
                Op::Add => Some(RangeElem::Concrete(
                    self_val.saturating_add(*other_val),
                    *loc,
                )),
                Op::Mul => Some(RangeElem::Concrete(
                    self_val.saturating_mul(*other_val),
                    *loc,
                )),
                Op::Div => Some(RangeElem::Concrete(self_val / other_val, *loc)),
                Op::Sub => Some(RangeElem::Concrete(
                    self_val.saturating_sub(*other_val),
                    *loc,
                )),
                Op::Mod => Some(RangeElem::Concrete(self_val % other_val, *loc)),
                Op::Min => {
                    if self_val < other_val {
                        Some(RangeElem::Concrete(*self_val, *loc))
                    } else {
                        Some(RangeElem::Concrete(*other_val, *loc))
                    }
                }
                Op::Max => {
                    if self_val > other_val {
                        Some(RangeElem::Concrete(*self_val, *loc))
                    } else {
                        Some(RangeElem::Concrete(*other_val, *loc))
                    }
                }
                _ => unreachable!("Comparator operations shouldn't exist in a range"),
            },
            (Self::SignedConcrete(self_val, loc), Self::SignedConcrete(other_val, _)) => match op {
                Op::Add => Some(RangeElem::SignedConcrete(
                    self_val.saturating_add(*other_val),
                    *loc,
                )),
                Op::Mul => Some(RangeElem::SignedConcrete(
                    self_val.saturating_mul(*other_val),
                    *loc,
                )),
                Op::Div => Some(RangeElem::SignedConcrete(*self_val / *other_val, *loc)),
                Op::Sub => Some(RangeElem::SignedConcrete(
                    self_val.saturating_sub(*other_val),
                    *loc,
                )),
                Op::Mod => Some(RangeElem::SignedConcrete(*self_val % *other_val, *loc)),
                Op::Min => {
                    if self_val < other_val {
                        Some(RangeElem::SignedConcrete(*self_val, *loc))
                    } else {
                        Some(RangeElem::SignedConcrete(*other_val, *loc))
                    }
                }
                Op::Max => {
                    if self_val > other_val {
                        Some(RangeElem::SignedConcrete(*self_val, *loc))
                    } else {
                        Some(RangeElem::SignedConcrete(*other_val, *loc))
                    }
                }
                _ => unreachable!("Comparator operations shouldn't exist in a range"),
            },
            (Self::Concrete(self_val, loc), Self::SignedConcrete(..)) => {
                let new_lhs =
                    Self::SignedConcrete(I256::try_from(*self_val).unwrap_or(I256::MAX), *loc);
                new_lhs.exec_op(other, op)
            }
            (Self::SignedConcrete(..), Self::Concrete(other_val, loc)) => {
                let new_rhs =
                    Self::SignedConcrete(I256::try_from(*other_val).unwrap_or(I256::MAX), *loc);
                self.exec_op(&new_rhs, op)
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeExpr {
    pub lhs: RangeExprElem,
    pub op: Op,
    pub rhs: RangeExprElem,
}

impl RangeExpr {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on();
        deps.extend(self.rhs.dependent_on());
        deps
    }

    pub fn eval(&self, analyzer: &impl AnalyzerLike) -> Option<RangeElem> {
        let lhs = self.lhs.clone().eval(analyzer);
        let rhs = self.rhs.clone().eval(analyzer);
        lhs.exec_op(&rhs, self.op)
    }

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        self.lhs.def_string(analyzer)
    }

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        let lhs_r_str = self.lhs.to_range_string(analyzer);
        let lhs_str = match self.lhs {
            RangeExprElem::Expr(_) => {
                let new_str = format!("({})", lhs_r_str.s);
                RangeElemString::new(new_str, lhs_r_str.loc)
            }
            _ => lhs_r_str,
        };

        let rhs_r_str = self.rhs.to_range_string(analyzer);

        let rhs_str = match self.rhs {
            RangeExprElem::Expr(_) => {
                let new_str = format!("({})", rhs_r_str.s);
                RangeElemString::new(new_str, rhs_r_str.loc)
            }
            _ => rhs_r_str,
        };

        if matches!(self.op, Op::Min | Op::Max) {
            RangeElemString::new(
                format!("{}({}, {})", self.op.to_string(), lhs_str.s, rhs_str.s),
                lhs_str.loc,
            )
        } else {
            RangeElemString::new(
                format!("{} {} {}", lhs_str.s, self.op.to_string(), rhs_str.s),
                lhs_str.loc,
            )
        }
    }

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        let mut lhs_str = self.lhs.bounds_range_string(analyzer);
        lhs_str.extend(self.rhs.bounds_range_string(analyzer));
        lhs_str
    }
}
