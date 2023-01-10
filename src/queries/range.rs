use crate::AnalyzerLike;
use crate::Builtin;
use crate::Concrete;
use crate::ContextVarNode;
use crate::NodeIdx;
use crate::VarType;
use ethers_core::types::I256;
use ethers_core::types::U256;
use solang_parser::pt::Loc;
use std::convert::TryFrom;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::Sub;

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

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Range {
    pub min: RangeElem,
    pub max: RangeElem,
}

impl Range {
    pub fn lte(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        Self {
            min: self.min,
            max: self.max.min(other.max, analyzer),
        }
    }

    pub fn gte(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        Self {
            min: self.min.max(other.min, analyzer),
            max: self.max,
        }
    }

    pub fn lt(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        Self {
            min: self.min,
            max: self.max.min(
                other.max - RangeElem::Concrete(1.into(), Loc::Implicit),
                analyzer,
            ),
        }
    }

    pub fn gt(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        Self {
            min: self.min.max(
                other.min + RangeElem::Concrete(1.into(), Loc::Implicit),
                analyzer,
            ),
            max: self.max,
        }
    }

    pub fn fn_from_op(op: Op) -> impl Fn(Range, Range) -> Range {
        match op {
            Op::Add => Self::add,
            Op::Sub => Self::sub,
            Op::Mul => Self::mul,
            Op::Div => Self::div,
            Op::Mod => Self::r#mod,
            _ => unreachable!("Min or Max in wrong place"),
        }
    }

    pub fn add(self, other: Self) -> Self {
        Self {
            min: self.min + other.min,
            max: self.max + other.max,
        }
    }

    pub fn sub(self, other: Self) -> Self {
        Self {
            min: self.min - other.max,
            max: self.max - other.min,
        }
    }

    pub fn mul(self, other: Self) -> Self {
        Self {
            min: self.min * other.min,
            max: self.max * other.max,
        }
    }

    pub fn div(self, other: Self) -> Self {
        Self {
            min: self.min / other.max,
            max: self.max / other.min,
        }
    }

    pub fn r#mod(self, other: Self) -> Self {
        Self {
            min: self.min % other.min,
            max: self.max % other.max,
        }
    }
}

// impl Add for Range {
//     fn add(self, other: Self) -> Self {
//         let min_expr = RangeExpr {
//             lhs: RangeExprElem::from(self.min),
//             op: Op::Add,
//             rhs: RangeExprElem::from(other.min),
//         };

//         let max_expr = RangeExpr {
//             lhs: RangeExprElem::from(self.max),
//             op: Op::Add,
//             rhs: RangeExprElem::from(other.max),
//         };

//         Self {
//             min: RangeElem::Complex(expr),
//             max: RangeElem::Complex(expr),
//         }
//     }
// }

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeElem {
    Concrete(U256, Loc),
    SignedConcrete(I256, Loc),
    Dynamic(NodeIdx, Loc),
    Complex(RangeExpr),
}

impl RangeElem {
    pub fn maybe_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use RangeElem::*;
        match (self, other) {
            (Concrete(s, _), Concrete(o, _)) => Some(s.cmp(o)),
            _ => None,
        }
    }

    pub fn min(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        match (self.eval(analyzer, false), other.eval(analyzer, false)) {
            (Self::Concrete(val, _), Self::Concrete(other_val, _)) => {
                if val < other_val {
                    self
                } else {
                    other
                }
            }
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Min,
                    rhs: RangeExprElem::from(other),
                };
                RangeElem::Complex(expr)
            }
        }
    }

    pub fn max(self, other: Self, analyzer: &impl AnalyzerLike) -> Self {
        match (self.eval(analyzer, true), other.eval(analyzer, true)) {
            (Self::Concrete(val, _), Self::Concrete(other_val, _)) => {
                if val > other_val {
                    self
                } else {
                    other
                }
            }
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Max,
                    rhs: RangeExprElem::from(other),
                };
                RangeElem::Complex(expr)
            }
        }
    }
}

impl Add for RangeElem {
    type Output = Self;

    fn add(self, other: RangeElem) -> Self {
        use RangeElem::*;
        match (&self, &other) {
            (Concrete(val, _), Concrete(val_other, loc)) => {
                Concrete(val.saturating_add(*val_other), *loc)
            }
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Add,
                    rhs: RangeExprElem::from(other),
                };
                Complex(expr)
            }
        }
    }
}

impl Sub for RangeElem {
    type Output = Self;

    fn sub(self, other: RangeElem) -> Self {
        use RangeElem::*;
        match (&self, &other) {
            (Concrete(val, _), Concrete(val_other, loc)) => {
                Concrete(val.saturating_sub(*val_other), *loc)
            }
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Sub,
                    rhs: RangeExprElem::from(other),
                };
                Complex(expr)
            }
        }
    }
}

impl Mul for RangeElem {
    type Output = Self;

    fn mul(self, other: RangeElem) -> Self {
        use RangeElem::*;
        match (&self, &other) {
            (Concrete(val, _), Concrete(val_other, loc)) => {
                Concrete(val.saturating_mul(*val_other), *loc)
            }
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Mul,
                    rhs: RangeExprElem::from(other),
                };
                Complex(expr)
            }
        }
    }
}

impl Div for RangeElem {
    type Output = Self;

    fn div(self, other: RangeElem) -> Self {
        use RangeElem::*;
        match (&self, &other) {
            (Concrete(val, _), Concrete(val_other, loc)) => Concrete(val.div(*val_other), *loc),
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Div,
                    rhs: RangeExprElem::from(other),
                };
                Complex(expr)
            }
        }
    }
}

impl Rem for RangeElem {
    type Output = Self;

    fn rem(self, other: RangeElem) -> Self {
        use RangeElem::*;
        match (&self, &other) {
            (Concrete(val, _), Concrete(val_other, loc)) => Concrete(val.rem(*val_other), *loc),
            _ => {
                let expr = RangeExpr {
                    lhs: RangeExprElem::from(self),
                    op: Op::Mod,
                    rhs: RangeExprElem::from(other),
                };
                Complex(expr)
            }
        }
    }
}

impl RangeElem {
    pub fn eval(&self, analyzer: &impl AnalyzerLike, eval_for_max: bool) -> Self {
        use RangeElem::*;
        match self {
            Concrete(..) => self.clone(),
            SignedConcrete(..) => self.clone(),
            Dynamic(idx, _) => {
                let cvar = ContextVarNode::from(*idx).underlying(analyzer);
                match &cvar.ty {
                    VarType::BuiltIn(_, maybe_range) => {
                        if let Some(range) = maybe_range {
                            if eval_for_max {
                                range.max.eval(analyzer, eval_for_max)
                            } else {
                                range.min.eval(analyzer, eval_for_max)
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
                if let Some(elem) = expr.eval(analyzer, eval_for_max) {
                    elem
                } else {
                    self.clone()
                }
            }
        }
    }

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeElem::*;
        match self {
            Complex(expr) => expr.def_string(analyzer),
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, _loc) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer);
                RangeElemString::new(cvar.name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
        }
    }

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeElem::*;
        match self {
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.name(analyzer);
                RangeElemString::new(name, *loc)
            }
            Complex(expr) => expr.to_range_string(analyzer),
        }
    }

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeElem::*;
        let mut range_strings = vec![];
        match self {
            Dynamic(idx, _loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.name(analyzer);
                if let Some(range) = as_var.range(analyzer) {
                    if let Some(ord) = range.min.maybe_ord(&range.max) {
                        match ord {
                            std::cmp::Ordering::Greater => {
                                let mut min = range.min.to_range_string(analyzer);
                                let max = range.max.to_range_string(analyzer);
                                min.s = format!("Always will revert, minimum bound for \"{}\" ({}) is required to be greater than max ({})", name, min.s, max.s);
                                range_strings.push(RangeString::new(min, max));
                                return range_strings;
                            }
                            _ => {}
                        }
                    }

                    let mut min = range.min.to_range_string(analyzer);
                    min.s = format!("\"{}\" ∈ {{{}, ", name, min.s);
                    let max = range.max.to_range_string(analyzer);

                    range_strings.push(RangeString::new(min, max));

                    range_strings.extend(range.min.bounds_range_string(analyzer));
                    range_strings.extend(range.max.bounds_range_string(analyzer));
                }
            }
            Complex(expr) => range_strings.extend(expr.bounds_range_string(analyzer)),
            _ => {}
        }

        range_strings
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeExprElem {
    Expr(Box<RangeExpr>),
    Concrete(U256, Loc),
    SignedConcrete(I256, Loc),
    Dynamic(NodeIdx, Loc),
}

impl From<RangeElem> for RangeExprElem {
    fn from(elem: RangeElem) -> Self {
        match elem {
            RangeElem::Complex(expr) => Self::Expr(Box::new(expr)),
            RangeElem::Concrete(val, loc) => Self::Concrete(val, loc),
            RangeElem::SignedConcrete(val, loc) => Self::SignedConcrete(val, loc),
            RangeElem::Dynamic(idx, loc) => Self::Dynamic(idx, loc),
        }
    }
}

impl RangeExprElem {
    pub fn eval(&self, analyzer: &impl AnalyzerLike, eval_for_max: bool) -> Self {
        use RangeExprElem::*;
        match self {
            Concrete(..) => self.clone(),
            SignedConcrete(..) => self.clone(),
            Dynamic(idx, _) => {
                let cvar = ContextVarNode::from(*idx).underlying(analyzer);
                match &cvar.ty {
                    VarType::BuiltIn(_, maybe_range) => {
                        if let Some(range) = maybe_range {
                            if eval_for_max {
                                Self::from(range.max.clone().eval(analyzer, eval_for_max))
                            } else {
                                Self::from(range.min.clone().eval(analyzer, eval_for_max))
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
                if let Some(elem) = expr.eval(analyzer, eval_for_max) {
                    Self::from(elem)
                } else {
                    self.clone()
                }
            }
        }
    }

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeExprElem::*;
        match self {
            Expr(expr) => expr.def_string(analyzer),
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, _loc) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer);
                RangeElemString::new(cvar.name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
        }
    }

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        use RangeExprElem::*;
        match self {
            Expr(expr) => expr.to_range_string(analyzer),
            Concrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            SignedConcrete(val, loc) => RangeElemString::new(val.to_string(), *loc),
            Dynamic(idx, loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.name(analyzer);
                RangeElemString::new(name, *loc)
            }
        }
    }

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeExprElem::*;
        match self {
            Dynamic(idx, loc) => RangeElem::Dynamic(*idx, *loc).bounds_range_string(analyzer),
            Expr(expr) => expr.bounds_range_string(analyzer),
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
    pub fn eval(&self, analyzer: &impl AnalyzerLike, eval_for_max: bool) -> Option<RangeElem> {
        let lhs = self.lhs.clone().eval(analyzer, eval_for_max);
        let rhs = self.rhs.clone().eval(analyzer, eval_for_max);
        lhs.exec_op(&rhs, self.op)
    }

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        self.lhs.def_string(analyzer)
    }

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        let lhs_str = self.lhs.to_range_string(analyzer);
        let op = self.op.to_string();
        let rhs_str = self.rhs.to_range_string(analyzer);

        RangeElemString::new(lhs_str.s + &op + &rhs_str.s, lhs_str.loc)
    }

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        let mut lhs_str = self.lhs.bounds_range_string(analyzer);
        lhs_str.extend(self.rhs.bounds_range_string(analyzer));
        lhs_str
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
            Min => "<min>".to_string(),
            Max => "<max>".to_string(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LenRange {
    pub min: RangeElem,
    pub max: RangeElem,
}

impl Range {
    pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
        match builtin {
            Builtin::Uint(size) => {
                if *size == 256 {
                    Some(Range {
                        min: RangeElem::Concrete(0.into(), Loc::Implicit),
                        max: RangeElem::Concrete(U256::MAX, Loc::Implicit),
                    })
                } else {
                    Some(Range {
                        min: RangeElem::Concrete(0.into(), Loc::Implicit),
                        max: RangeElem::Concrete(
                            U256::from(2).pow(U256::from(*size)) - 1,
                            Loc::Implicit,
                        ),
                    })
                }
            }
            _ => None,
        }
    }
}
