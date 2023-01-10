use crate::{AnalyzerLike, Builtin, ContextVarNode, NodeIdx, VarType};
use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;
use std::convert::TryFrom;
use std::ops::{Add, Div, Mul, Rem, Sub};

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
            Op::Mod => Self::r#mod,
            Op::Min => Self::min,
            Op::Max => Self::max,
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

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeElem {
    // TODO: add max or size to this element to do proper bounds (except unchecked)
    Concrete(U256, Loc),
    SignedConcrete(I256, Loc),
    Dynamic(NodeIdx, DynamicRangeSide, Loc),
    Complex(RangeExpr),
}

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

impl RangeElem {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Dynamic(idx, ..) => vec![ContextVarNode::from(*idx)],
            Self::Complex(expr) => expr.dependent_on(),
            _ => vec![],
        }
    }

    pub fn maybe_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use RangeElem::*;
        match (self, other) {
            (Concrete(s, _), Concrete(o, _)) => Some(s.cmp(o)),
            _ => None,
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

impl RangeElem {
    pub fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
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
                                    Self::from(range.min.clone().eval(analyzer))
                                }
                                DynamicRangeSide::Max => {
                                    Self::from(range.max.clone().eval(analyzer))
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

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
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

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
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

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeElem::*;
        let mut range_strings = vec![];
        match self {
            Dynamic(idx, _range_side, _loc) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.display_name(analyzer);
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

impl RangeExprElem {
    pub fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Dynamic(idx, ..) => vec![ContextVarNode::from(*idx)],
            Self::Expr(expr) => expr.dependent_on(),
            _ => vec![],
        }
    }

    pub fn eval(&self, analyzer: &impl AnalyzerLike) -> Self {
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
                                    Self::from(range.min.clone().eval(analyzer))
                                }
                                DynamicRangeSide::Max => {
                                    Self::from(range.max.clone().eval(analyzer))
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

    pub fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
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

    pub fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
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

    pub fn bounds_range_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        use RangeExprElem::*;
        match self {
            Dynamic(idx, range_side, loc) => {
                RangeElem::Dynamic(*idx, *range_side, *loc).bounds_range_string(analyzer)
            }
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
            Min => "min".to_string(),
            Max => "max".to_string(),
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
