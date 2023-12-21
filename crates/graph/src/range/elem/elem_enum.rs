use std::hash::Hasher;
use std::hash::Hash;
use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{
        collapse, MaybeCollapsed, RangeConcrete, RangeDyn, RangeElem, RangeExpr, RangeOp, Reference,
    },
    GraphBackend, GraphError,
};
use solang_parser::pt::Loc;

use shared::{RangeArenaIdx, NodeIdx};

use ethers_core::types::I256;

use std::{
    collections::BTreeMap,
    ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub},
};

/// A core range element.
#[derive(Default, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Reference(Reference<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(RangeDyn<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    Concrete(RangeConcrete<T>),
    /// A range element that is an expression composed of other range elements
    Expr(RangeExpr<T>),
    /// A range element that is a pointer to another expression in an arena
    Arena(RangeArenaIdx),
    /// A null range element useful in range expressions that dont have a rhs
    #[default]
    Null,
}

impl Hash for Elem<Concrete> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Elem::Reference(r) => r.hash(state),
            Elem::Concrete(c) => c.hash(state),
            Elem::Expr(expr) => expr.hash(state),
            Elem::ConcreteDyn(d) => d.hash(state),
            Elem::Null => (-1i32).hash(state),
            Elem::Arena(idx) => idx.hash(state),
        }
    }
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
            Elem::Null => {},
            Elem::Arena(_) => todo!()
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
            Elem::ConcreteDyn(a) => Some(a.clone()),
            _ => None,
        }
    }

    pub fn is_conc(&self) -> bool {
        match self {
            Elem::Concrete(_a) => true,
            Elem::ConcreteDyn(a) => {
                a.len.maybe_concrete().is_some()
                    && a.val
                        .iter()
                        .all(|(key, (val, _))| key.is_conc() && val.is_conc())
            }
            Elem::Expr(expr) => expr.lhs.is_conc() && expr.rhs.is_conc(),
            _ => false,
        }
    }
}

impl<T: Ord> Elem<T> {
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        match self {
            Self::Reference(d) => d.idx == node_idx,
            Self::Concrete(_) => false,
            Self::Expr(expr) => expr.contains_node(node_idx),
            Self::ConcreteDyn(d) => d.contains_node(node_idx),
            Self::Null => false,
            Elem::Arena(_) => todo!()
        }
    }

    pub fn expect_into_expr(self) -> RangeExpr<T> {
        match self {
            Self::Expr(expr) => expr,
            _ => panic!("Not expression"),
        }
    }

    pub fn dyn_map(&self) -> Option<&BTreeMap<Self, (Self, usize)>> {
        match self {
            Self::ConcreteDyn(dyn_range) => Some(&dyn_range.val),
            _ => None,
        }
    }

    pub fn dyn_map_mut(&mut self) -> Option<&mut BTreeMap<Self, (Self, usize)>> {
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

    /// Creates a new range element that is a memcopy of another
    pub fn memcopy(self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Memcopy, Elem::Null);
        Elem::Expr(expr)
    }

    /// Creates a new range element that applies a setting of indices of a memory object
    pub fn set_indices(self, other: RangeDyn<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::SetIndices, Elem::ConcreteDyn(other));
        Elem::Expr(expr)
    }

    /// Creates a new range element that sets the length of a memory object
    pub fn set_length(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::SetLength, other);
        Elem::Expr(expr)
    }

    /// Gets the length of a memory object
    pub fn get_length(self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::GetLength, Elem::Null);
        Elem::Expr(expr)
    }

    /// Gets the length of a memory object
    pub fn get_index(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::GetIndex, other);
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

impl<T: Ord> Add for Elem<T> {
    type Output = Self;

    fn add(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Sub for Elem<T> {
    type Output = Self;

    fn sub(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Mul for Elem<T> {
    type Output = Self;

    fn mul(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Div for Elem<T> {
    type Output = Self;

    fn div(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Shl for Elem<T> {
    type Output = Self;

    fn shl(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shl, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Shr for Elem<T> {
    type Output = Self;

    fn shr(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shr, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Rem for Elem<T> {
    type Output = Self;

    fn rem(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mod, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitAnd for Elem<T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitAnd, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitOr for Elem<T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitOr, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitXor for Elem<T> {
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
    pub fn dearenaize<'a>(&self, analyzer: &'a impl GraphBackend) -> &'a Self {
        match self {
            Self::Arena(arena_idx) => &analyzer.range_arena().ranges[*arena_idx],
            _ => unreachable!()
        }
    }

    pub fn dearenaize_mut<'a> (&self, analyzer: &'a mut impl GraphBackend) -> &'a mut Self {
        match self {
            Self::Arena(arena_idx) => &mut analyzer.range_arena_mut().ranges[*arena_idx],
            _ => unreachable!()
        }
    }

    pub fn arena_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => a == b,
            (Self::Concrete(a), Self::Concrete(b)) => a == b,
            (Self::ConcreteDyn(a), Self::ConcreteDyn(b)) => {
                a.len == b.len
                && a.val.len() == b.val.len()
                && a.val.iter().zip(b.val.iter()).all(|((a, op_a), (b, op_b))| a.arena_eq(b) && op_a == op_b)
            },
            (Self::Reference(a), Self::Reference(b)) => a == b,
            (Self::Expr(a), Self::Expr(b)) => {
                a.lhs.arena_eq(&b.lhs)
                && a.rhs.arena_eq(&b.rhs)
                && a.op == b.op
            },
            (Elem::Null, Elem::Null) => true,
            _ => false,
        }
    }
    pub fn as_bytes(&self, analyzer: &impl GraphBackend, maximize: bool) -> Option<Vec<u8>> {
        let evaled = if maximize {
            self.maximize(analyzer).ok()?
        } else {
            self.minimize(analyzer).ok()?
        };

        match evaled {
            Elem::Concrete(c) => c.as_bytes(analyzer, maximize),
            Elem::ConcreteDyn(c) => c.as_bytes(analyzer, maximize),
            _ => None,
        }
    }

    pub fn overlaps(
        &self,
        other: &Self,
        eval: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<bool>, GraphError> {
        match (self, other) {
            (Elem::Concrete(s), Elem::Concrete(o)) => Ok(Some(o.val == s.val)),
            (Elem::Reference(s), Elem::Reference(o)) => {
                if eval {
                    let lhs_min = s.minimize(analyzer)?;
                    let rhs_max = o.maximize(analyzer)?;

                    match lhs_min.range_ord(&rhs_max, analyzer) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = s.maximize(analyzer)?;
                            let rhs_min = o.minimize(analyzer)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(&rhs_min, analyzer),
                                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                            )))
                        }
                        Some(std::cmp::Ordering::Equal) => Ok(Some(true)),
                        _ => Ok(Some(false)),
                    }
                } else if s == o {
                    Ok(Some(true))
                } else {
                    Ok(None)
                }
            }
            (Elem::Reference(s), c @ Elem::Concrete(_)) => {
                if eval {
                    let lhs_min = s.minimize(analyzer)?;

                    match lhs_min.range_ord(c, analyzer) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = s.maximize(analyzer)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(c, analyzer),
                                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                            )))
                        }
                        Some(std::cmp::Ordering::Equal) => Ok(Some(true)),
                        _ => Ok(Some(false)),
                    }
                } else {
                    Ok(None)
                }
            }
            (Elem::Concrete(_), Elem::Reference(_)) => other.overlaps(self, eval, analyzer),
            _ => Ok(None),
        }
    }
    pub fn overlaps_dual(
        &self,
        rhs_min: &Self,
        rhs_max: &Self,
        eval: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<bool>, GraphError> {
        match self {
            Self::Reference(d) => {
                if eval {
                    let lhs_min = d.minimize(analyzer)?;
                    let rhs_max = rhs_max.maximize(analyzer)?;

                    match lhs_min.range_ord(&rhs_max, analyzer) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = d.maximize(analyzer)?;
                            let rhs_min = rhs_min.minimize(analyzer)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(&rhs_min, analyzer),
                                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                            )))
                        }
                        Some(std::cmp::Ordering::Equal) => Ok(Some(true)),
                        _ => Ok(Some(false)),
                    }
                } else if self == rhs_min || self == rhs_max {
                    Ok(Some(true))
                } else {
                    Ok(None)
                }
            }
            Self::Concrete(_) => match rhs_min.range_ord(self, analyzer) {
                Some(std::cmp::Ordering::Less) => Ok(Some(matches!(
                    rhs_max.range_ord(self, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                ))),
                Some(std::cmp::Ordering::Equal) => Ok(Some(true)),
                _ => Ok(Some(false)),
            },
            _ => Ok(None),
        }
    }
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
            Self::Arena(_) => todo!(),
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
            Elem::ConcreteDyn(d) => {
                write!(f, "{{len: {}, values: {{", d.len)?;
                d.val
                    .iter()
                    .try_for_each(|(key, (val, op))| write!(f, " {key}: ({val}, {op}),"))?;
                write!(f, "}}}}")
            }
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
            Elem::Arena(idx) => write!(f, "arena_idx_{idx}"),
            Elem::Null => write!(f, ""),
        }
    }
}

impl RangeElem<Concrete> for Elem<Concrete> {
    type GraphError = GraphError;

    fn arenaize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        match self {
            Self::Arena(_) => return Ok(()),
            Self::Reference(d) => d.arenaize(analyzer)?,
            Self::ConcreteDyn(d) => d.arenaize(analyzer)?,
            Self::Expr(expr) => {
                expr.arenaize(analyzer)?;
            },
            _ => {}
        }

        let self_take = std::mem::take(self);
        *self = Elem::Arena(analyzer.range_arena_idx_or_upsert(self_take));
        Ok(())
    }

    fn range_eq(&self, other: &Self, analyzer: &impl GraphBackend) -> bool {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => {
                a == b
            },
            (Self::Concrete(a), Self::Concrete(b)) => a.range_eq(b, analyzer),
            (Self::ConcreteDyn(a), Self::ConcreteDyn(b)) => a.range_eq(b, analyzer),
            (Self::Reference(a), Self::Reference(b)) => a.idx == b.idx,
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self, analyzer: &impl GraphBackend) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => {
                if a == b {
                    Some(std::cmp::Ordering::Equal)
                } else {
                    self.dearenaize(analyzer).range_ord(other.dearenaize(analyzer), analyzer)
                }
            },
            (Self::Concrete(a), Self::Concrete(b)) => a.range_ord(b, analyzer),
            (Self::Reference(a), Self::Reference(b)) => a.range_ord(b, analyzer),
            (Elem::Null, Elem::Null) => None,
            (_a, Elem::Null) => Some(std::cmp::Ordering::Greater),
            (Elem::Null, _a) => Some(std::cmp::Ordering::Less),
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
            Self::Arena(_) => self.dearenaize(analyzer).flatten(maximize, analyzer),
        }
    }

    fn cache_flatten(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        if self.is_flatten_cached(analyzer) {
            return Ok(())
        }
        match self {
            Self::Reference(d) => d.cache_flatten(analyzer),
            Self::Concrete(c) => c.cache_flatten(analyzer),
            Self::Expr(expr) => expr.cache_flatten(analyzer),
            Self::ConcreteDyn(d) => d.cache_flatten(analyzer),
            Self::Null => Ok(()),
            Self::Arena(idx) => {
                let idx = *idx;
                let mut dearenaized = self.dearenaize(analyzer).clone();
                dearenaized.cache_flatten(analyzer)?;
                analyzer.range_arena_mut().ranges[idx] = dearenaized;
                Ok(())
            },
        }
    }

    fn is_flatten_cached(&self, analyzer: &impl GraphBackend,) -> bool {
        match self {
            Self::Reference(d) => d.is_flatten_cached(analyzer),
            Self::Concrete(c) => c.is_flatten_cached(analyzer),
            Self::Expr(expr) => expr.is_flatten_cached(analyzer),
            Self::ConcreteDyn(d) => d.is_flatten_cached(analyzer),
            Self::Null => true,
            Self::Arena(_) => self.dearenaize(analyzer).is_flatten_cached(analyzer),
        }
    }

    fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        match self {
            Self::Reference(d) => d.dependent_on(analyzer),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(analyzer),
            Self::ConcreteDyn(d) => d.dependent_on(analyzer),
            Self::Null => vec![],
            Self::Arena(_) => self.dearenaize(analyzer).dependent_on(analyzer),
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
            Self::Arena(_) => self.dearenaize(analyzer).recursive_dependent_on(analyzer),
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
            Self::Arena(_) => self.dearenaize(analyzer).has_cycle(seen, analyzer),
        }
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx, analyzer: &mut impl GraphBackend) {
        match self {
            Self::Reference(ref mut d) => {
                if d.idx == node_idx {
                    d.idx = new_idx
                }
            }
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.filter_recursion(node_idx, new_idx, analyzer),
            Self::ConcreteDyn(d) => d.filter_recursion(node_idx, new_idx, analyzer),
            Self::Null => {}
            Self::Arena(idx) => {
                let idx = *idx;
                let mut dearenaized = self.dearenaize(analyzer).clone();
                dearenaized.filter_recursion(node_idx, new_idx,analyzer);
                analyzer.range_arena_mut().ranges[idx] = dearenaized;
            },
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
            Arena(_) => self.dearenaize(analyzer).maximize(analyzer)?,
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
            Arena(_) => self.dearenaize(analyzer).minimize(analyzer)?,
        };
        Ok(res)
    }

    fn simplify_maximize(
        &self,
        seen_ops: &mut BTreeMap<Elem<Concrete>, Elem<Concrete>>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(res) = seen_ops.get(self) {
            return Ok(res.clone());
        }

        use Elem::*;
        match self {
            Reference(dy) => dy.simplify_maximize(seen_ops, analyzer),
            Concrete(inner) => inner.simplify_maximize(seen_ops, analyzer),
            ConcreteDyn(inner) => inner.simplify_maximize(seen_ops, analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    collapsed.simplify_maximize(seen_ops, analyzer)
                }
                _ => expr.simplify_maximize(seen_ops, analyzer),
            },
            Null => Ok(Elem::Null),
            Arena(_) => self.dearenaize(analyzer).simplify_maximize(seen_ops, analyzer),
        }
    }

    fn simplify_minimize(
        &self,
        seen_ops: &mut BTreeMap<Elem<Concrete>, Elem<Concrete>>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(res) = seen_ops.get(self) {
            return Ok(res.clone());
        }

        use Elem::*;
        let res = match self {
            Reference(dy) => dy.simplify_minimize(seen_ops, analyzer),
            Concrete(inner) => inner.simplify_minimize(seen_ops, analyzer),
            ConcreteDyn(inner) => inner.simplify_minimize(seen_ops, analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    collapsed.simplify_minimize(seen_ops, analyzer)
                }
                _ => expr.simplify_minimize(seen_ops, analyzer),
            },
            Null => Ok(Elem::Null),
            Arena(_) => self.dearenaize(analyzer).simplify_minimize(seen_ops, analyzer),
        }?;

        seen_ops.insert(self.clone(), res.clone());
        Ok(res)
    }

    fn cache_maximize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_maximize(analyzer),
            Concrete(inner) => inner.cache_maximize(analyzer),
            ConcreteDyn(inner) => inner.cache_maximize(analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(mut collapsed) => {
                    collapsed.cache_minimize(analyzer)?;
                    *self = collapsed;
                    Ok(())
                }
                _ => expr.cache_maximize(analyzer),
            },
            Null => Ok(()),
            Arena(idx) => {
                let idx = *idx;
                let mut dearenaized = self.dearenaize(analyzer).clone();
                dearenaized.cache_maximize(analyzer)?;
                analyzer.range_arena_mut().ranges[idx] = dearenaized;
                Ok(())
            },
        }
    }

    fn cache_minimize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_minimize(analyzer),
            Concrete(inner) => inner.cache_minimize(analyzer),
            ConcreteDyn(inner) => inner.cache_minimize(analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(mut collapsed) => {
                    collapsed.cache_minimize(analyzer)?;
                    *self = collapsed;
                    Ok(())
                }
                _ => expr.cache_minimize(analyzer),
            },
            Null => Ok(()),
            Arena(idx) => {
                let idx = *idx;
                let mut dearenaized = self.dearenaize(analyzer).clone();
                dearenaized.cache_minimize(analyzer)?;
                analyzer.range_arena_mut().ranges[idx] = dearenaized;
                Ok(())
            },
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
            Arena(_idx) => {},
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
