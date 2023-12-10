use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{RangeConcrete, RangeDyn, RangeElem, RangeExpr, RangeOp, Reference},
    GraphBackend, GraphError,
};
use solang_parser::pt::Loc;

use shared::NodeIdx;

use ethers_core::types::I256;

use std::{
    collections::BTreeMap,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
};

/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Reference(Reference<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(Box<RangeDyn<T>>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    Concrete(RangeConcrete<T>),
    /// A range element that is an expression composed of other range elements
    Expr(RangeExpr<T>),
    /// A null range element useful in range expressions that dont have a rhs
    Null,
}

impl<T: Clone> Elem<T> {
    pub fn replace_dep(&mut self, to_replace: NodeIdx, replacement: Self) {
        match self {
            Elem::Reference(Reference { idx, .. }) => {
                if *idx == to_replace {
                    *self = replacement;
                }
            }
            Elem::Concrete(_) => {}
            Elem::Expr(expr) => {
                expr.lhs.replace_dep(to_replace, replacement.clone());
                expr.rhs.replace_dep(to_replace, replacement);
                expr.maximized = None;
                expr.minimized = None;
            }
            Elem::ConcreteDyn(_d) => todo!(),
            Elem::Null => {}
        }
    }

    pub fn node_idx(&self) -> Option<NodeIdx> {
        match self {
            Self::Reference(Reference { idx, .. }) => Some(*idx),
            _ => None,
        }
    }

    pub fn concrete(&self) -> Option<T> {
        match self {
            Self::Concrete(RangeConcrete { val: c, .. }) => Some(c.clone()),
            _ => None,
        }
    }

    pub fn maybe_concrete(&self) -> Option<RangeConcrete<T>> {
        match self {
            Elem::Concrete(a) => Some(a.clone()),
            _ => None,
        }
    }

    pub fn maybe_concrete_value(&self) -> Option<RangeConcrete<T>> {
        match self {
            Elem::Concrete(a) => Some(a.clone()),
            _ => None,
        }
    }

    pub fn maybe_range_dyn(&self) -> Option<RangeDyn<T>> {
        match self {
            Elem::ConcreteDyn(a) => Some(*a.clone()),
            _ => None,
        }
    }
}

impl<T> Elem<T> {
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        match self {
            Self::Reference(d) => d.idx == node_idx,
            Self::Concrete(_) => false,
            Self::Expr(expr) => expr.contains_node(node_idx),
            Self::ConcreteDyn(d) => d.contains_node(node_idx),
            Self::Null => false,
        }
    }

    pub fn expect_into_expr(self) -> RangeExpr<T> {
        match self {
            Self::Expr(expr) => expr,
            _ => panic!("Not expression"),
        }
    }

    pub fn dyn_map(&self) -> Option<&BTreeMap<Self, Self>> {
        match self {
            Self::ConcreteDyn(dyn_range) => Some(&dyn_range.val),
            _ => None,
        }
    }

    pub fn dyn_map_mut(&mut self) -> Option<&mut BTreeMap<Self, Self>> {
        match self {
            Self::ConcreteDyn(ref mut dyn_range) => Some(&mut dyn_range.val),
            _ => None,
        }
    }

    /// Creates a new range element that is a cast from one type to another
    pub fn cast(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Cast, other);
        Elem::Expr(expr)
    }

    pub fn concat(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Concat, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the minimum of two range elements
    pub fn min(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Min, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the maximum of two range elements
    pub fn max(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Max, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of equality of two range elements
    pub fn eq(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Eq, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of inequality of two range elements
    pub fn neq(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Neq, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is one range element to the power of another
    pub fn pow(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Exp, other);
        Elem::Expr(expr)
    }
}

impl<T> From<Reference<T>> for Elem<T> {
    fn from(dy: Reference<T>) -> Self {
        Elem::Reference(dy)
    }
}

impl<T> From<RangeConcrete<T>> for Elem<T> {
    fn from(c: RangeConcrete<T>) -> Self {
        Elem::Concrete(c)
    }
}

impl<T> Add for Elem<T> {
    type Output = Self;

    fn add(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(false), other);
        Self::Expr(expr)
    }
}

impl<T> Sub for Elem<T> {
    type Output = Self;

    fn sub(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(false), other);
        Self::Expr(expr)
    }
}

impl<T> Mul for Elem<T> {
    type Output = Self;

    fn mul(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(false), other);
        Self::Expr(expr)
    }
}

impl<T> Div for Elem<T> {
    type Output = Self;

    fn div(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(false), other);
        Self::Expr(expr)
    }
}

impl<T> Shl for Elem<T> {
    type Output = Self;

    fn shl(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shl, other);
        Self::Expr(expr)
    }
}

impl<T> Shr for Elem<T> {
    type Output = Self;

    fn shr(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shr, other);
        Self::Expr(expr)
    }
}

impl<T> Rem for Elem<T> {
    type Output = Self;

    fn rem(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mod, other);
        Self::Expr(expr)
    }
}

impl<T> BitAnd for Elem<T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitAnd, other);
        Self::Expr(expr)
    }
}

impl<T> BitOr for Elem<T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitOr, other);
        Self::Expr(expr)
    }
}

impl<T> BitXor for Elem<T> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitXor, other);
        Self::Expr(expr)
    }
}

impl<T> From<NodeIdx> for Elem<T> {
    fn from(idx: NodeIdx) -> Self {
        Elem::Reference(Reference::new(idx))
    }
}

impl Elem<Concrete> {
    pub fn is_negative(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let res = match self {
            Elem::Concrete(RangeConcrete {
                val: Concrete::Int(_, val),
                ..
            }) if val < &I256::zero() => true,
            Elem::Reference(dy) => {
                if maximize {
                    dy.maximize(analyzer)?.is_negative(maximize, analyzer)?
                } else {
                    dy.minimize(analyzer)?.is_negative(maximize, analyzer)?
                }
            }
            Elem::Expr(expr) => {
                if maximize {
                    expr.maximize(analyzer)?.is_negative(maximize, analyzer)?
                } else {
                    expr.minimize(analyzer)?.is_negative(maximize, analyzer)?
                }
            }
            _ => false,
        };
        Ok(res)
    }

    pub fn pre_evaled_is_negative(&self) -> bool {
        matches!(self, Elem::Concrete(RangeConcrete { val: Concrete::Int(_, val), ..}) if val < &I256::zero())
    }

    pub fn inverse_if_boolean(&self) -> Option<Self> {
        match self {
            Self::Reference(Reference { idx: _, .. }) => Some(Elem::Expr(RangeExpr::new(
                self.clone(),
                RangeOp::Not,
                Elem::Null,
            ))),
            Self::Concrete(_) => Some(Elem::Expr(RangeExpr::new(
                self.clone(),
                RangeOp::Not,
                Elem::Null,
            ))),
            Self::Expr(expr) => Some(Elem::Expr(expr.inverse_if_boolean()?)),
            Self::ConcreteDyn(_d) => None,
            Self::Null => None,
        }
    }
}

impl From<Concrete> for Elem<Concrete> {
    fn from(c: Concrete) -> Self {
        Elem::Concrete(RangeConcrete {
            val: c,
            loc: Loc::Implicit,
        })
    }
}

impl From<ContextVarNode> for Elem<Concrete> {
    fn from(c: ContextVarNode) -> Self {
        Elem::Reference(Reference::new(c.into()))
    }
}

impl std::fmt::Display for Elem<Concrete> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Elem::Reference(Reference { idx, .. }) => write!(f, "idx_{}", idx.index()),
            Elem::ConcreteDyn(..) => write!(f, "range_elem"),
            Elem::Concrete(RangeConcrete { val, .. }) => {
                write!(f, "{}", val.as_string())
            }
            Elem::Expr(RangeExpr { lhs, op, rhs, .. }) => match op {
                RangeOp::Min | RangeOp::Max => {
                    write!(f, "{}{{{}, {}}}", op.to_string(), lhs, rhs)
                }
                RangeOp::Cast => match &**rhs {
                    Elem::Concrete(RangeConcrete { val, .. }) => {
                        write!(
                            f,
                            "{}({}, {})",
                            op.to_string(),
                            lhs,
                            val.as_builtin().basic_as_string()
                        )
                    }
                    _ => write!(f, "{}({}, {})", op.to_string(), lhs, rhs),
                },
                RangeOp::BitNot => {
                    write!(f, "~{}", lhs)
                }
                _ => write!(f, "({} {} {})", lhs, op.to_string(), rhs),
            },
            _ => write!(f, ""),
        }
    }
}

impl RangeElem<Concrete> for Elem<Concrete> {
    type GraphError = GraphError;

    fn range_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Concrete(a), Self::Concrete(b)) => a.range_eq(b),
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Concrete(a), Self::Concrete(b)) => a.range_ord(b),
            (Self::Reference(a), Self::Reference(b)) => a.range_ord(b),
            _ => None,
        }
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        match self {
            Self::Reference(d) => d.flatten(maximize, analyzer),
            Self::Concrete(c) => c.flatten(maximize, analyzer),
            Self::Expr(expr) => expr.flatten(maximize, analyzer),
            Self::ConcreteDyn(d) => d.flatten(maximize, analyzer),
            Self::Null => Ok(Elem::Null),
        }
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Reference(d) => d.dependent_on(),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(),
            Self::ConcreteDyn(d) => d.dependent_on(),
            Self::Null => vec![],
        }
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        match self {
            Self::Reference(d) => d.recursive_dependent_on(analyzer),
            Self::Concrete(_) => Ok(vec![]),
            Self::Expr(expr) => expr.recursive_dependent_on(analyzer),
            Self::ConcreteDyn(d) => d.recursive_dependent_on(analyzer),
            Self::Null => Ok(vec![]),
        }
    }

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, Self::GraphError> {
        match self {
            Self::Reference(d) => d.has_cycle(seen, analyzer),
            Self::Concrete(_) => Ok(false),
            Self::Expr(expr) => expr.has_cycle(seen, analyzer),
            Self::ConcreteDyn(d) => d.has_cycle(seen, analyzer),
            Self::Null => Ok(false),
        }
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        match self {
            Self::Reference(d) => d.update_deps(mapping),
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.update_deps(mapping),
            Self::ConcreteDyn(d) => d.update_deps(mapping),
            Self::Null => {}
        }
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        match self {
            Self::Reference(ref mut d) => {
                if d.idx == node_idx {
                    d.idx = new_idx
                }
            }
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.filter_recursion(node_idx, new_idx),
            Self::ConcreteDyn(d) => d.filter_recursion(node_idx, new_idx),
            Self::Null => {}
        }
    }

    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.maximize(analyzer)?,
            Concrete(inner) => inner.maximize(analyzer)?,
            ConcreteDyn(inner) => inner.maximize(analyzer)?,
            Expr(expr) => expr.maximize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.minimize(analyzer)?,
            Concrete(inner) => inner.minimize(analyzer)?,
            ConcreteDyn(inner) => inner.minimize(analyzer)?,
            Expr(expr) => expr.minimize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.simplify_maximize(exclude, analyzer),
            Concrete(inner) => inner.simplify_maximize(exclude, analyzer),
            ConcreteDyn(inner) => inner.simplify_maximize(exclude, analyzer),
            Expr(expr) => expr.simplify_maximize(exclude, analyzer),
            Null => Ok(Elem::Null),
        }
    }

    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.simplify_minimize(exclude, analyzer),
            Concrete(inner) => inner.simplify_minimize(exclude, analyzer),
            ConcreteDyn(inner) => inner.simplify_minimize(exclude, analyzer),
            Expr(expr) => expr.simplify_minimize(exclude, analyzer),
            Null => Ok(Elem::Null),
        }
    }

    fn cache_maximize(&mut self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_maximize(analyzer),
            Concrete(inner) => inner.cache_maximize(analyzer),
            ConcreteDyn(inner) => inner.cache_maximize(analyzer),
            Expr(expr) => expr.cache_maximize(analyzer),
            Null => Ok(()),
        }
    }

    fn cache_minimize(&mut self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_minimize(analyzer),
            Concrete(inner) => inner.cache_minimize(analyzer),
            ConcreteDyn(inner) => inner.cache_minimize(analyzer),
            Expr(expr) => expr.cache_minimize(analyzer),
            Null => Ok(()),
        }
    }
    fn uncache(&mut self) {
        use Elem::*;
        match self {
            Reference(dy) => dy.uncache(),
            Concrete(inner) => inner.uncache(),
            ConcreteDyn(inner) => inner.uncache(),
            Expr(expr) => expr.uncache(),
            Null => {}
        }
    }

    fn contains_op_set(
        &self,
        max: bool,
        op_set: &[RangeOp],
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.contains_op_set(max, op_set, analyzer),
            Concrete(inner) => inner.contains_op_set(max, op_set, analyzer),
            ConcreteDyn(inner) => inner.contains_op_set(max, op_set, analyzer),
            Expr(expr) => expr.contains_op_set(max, op_set, analyzer),
            Null => Ok(false),
        }
    }
}

impl Elem<Concrete> {
    pub fn wrapping_add(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_sub(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_mul(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_div(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(true), other);
        Self::Expr(expr)
    }

    /// Creates a logical AND of two range elements
    pub fn and(self, other: Self) -> Self {
        let expr = RangeExpr::<Concrete>::new(self, RangeOp::And, other);
        Self::Expr(expr)
    }

    /// Creates a logical OR of two range elements
    pub fn or(self, other: Self) -> Self {
        let expr = RangeExpr::<Concrete>::new(self, RangeOp::Or, other);
        Self::Expr(expr)
    }

    pub fn maybe_elem_min(&self) -> Option<Self> {
        match self {
            Elem::Concrete(RangeConcrete { val, .. }) => Some(Elem::from(Concrete::min(val)?)),
            _ => None,
        }
    }

    pub fn maybe_elem_max(&self) -> Option<Self> {
        match self {
            Elem::Concrete(RangeConcrete { val, .. }) => Some(Elem::from(Concrete::max(val)?)),
            _ => None,
        }
    }
}