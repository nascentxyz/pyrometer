use crate::elem::{MinMaxed, RangeArenaLike};
use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeConcrete, RangeDyn, RangeElem, RangeExpr, RangeOp, Reference},
    GraphBackend, GraphError,
};
use shared::{NodeIdx, RangeArena};

use ethers_core::types::I256;

use std::collections::BTreeMap;

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
            Elem::Concrete(RangeConcrete { val, .. }) => {
                Some(Elem::from(Concrete::min_of_type(val)?))
            }
            _ => None,
        }
    }

    pub fn maybe_elem_max(&self) -> Option<Self> {
        match self {
            Elem::Concrete(RangeConcrete { val, .. }) => {
                Some(Elem::from(Concrete::max_of_type(val)?))
            }
            _ => None,
        }
    }

    pub fn arena_graph_node_label(&self) -> String {
        match self {
            Elem::Reference(reference) => {
                format!("Ref-CVar{}", reference.idx.index())
            }
            Elem::ConcreteDyn(_range_dyn) => {
                format!("concdyn-{}", self)
            }
            Elem::Concrete(_range_concrete) => {
                format!("conc-{}", self)
            }
            Elem::Expr(_range_expr) => {
                // Unbox and check the lhs and rhs to see if they are arena indices
                format!("expr-{}", &self)
            }
            Elem::Arena(arena_idx) => {
                format!("Arena({})", arena_idx)
            }
            Elem::Null => {
                todo!()
            }
        }
    }
}

impl<T: Clone> Elem<T> {
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
    pub fn assert_nonnull(&self) {
        match self {
            Elem::Expr(expr) => {
                expr.lhs.assert_nonnull();
                expr.rhs.assert_nonnull();
            }
            Elem::Null => panic!("was null"),
            _ => {}
        }
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        match self {
            Self::Reference(d) => d.idx == node_idx,
            Self::Concrete(_) => false,
            Self::Expr(expr) => expr.contains_node(node_idx),
            Self::ConcreteDyn(d) => d.contains_node(node_idx),
            Self::Null => false,
            Elem::Arena(_) => todo!(),
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

impl Elem<Concrete> {
    pub fn replace_dep(
        &mut self,
        to_replace: NodeIdx,
        replacement: Self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Self>,
    ) {
        match self {
            Elem::Reference(Reference { idx, .. }) => {
                if *idx == to_replace {
                    *self = replacement;
                }
            }
            Elem::Concrete(_) => {}
            Elem::Expr(expr) => {
                expr.lhs
                    .replace_dep(to_replace, replacement.clone(), analyzer, arena);
                expr.rhs
                    .replace_dep(to_replace, replacement, analyzer, arena);
                expr.maximized = None;
                expr.minimized = None;
            }
            Elem::ConcreteDyn(d) => {
                d.len
                    .replace_dep(to_replace, replacement.clone(), analyzer, arena);
                let vals = std::mem::take(&mut d.val);
                d.val = vals
                    .into_iter()
                    .map(|(mut k, (mut v, op))| {
                        k.replace_dep(to_replace, replacement.clone(), analyzer, arena);
                        v.replace_dep(to_replace, replacement.clone(), analyzer, arena);
                        (k, (v, op))
                    })
                    .collect();
            }
            Elem::Null => {}
            Elem::Arena(_) => {
                let mut cloned = self.dearenaize_clone(arena);
                cloned.replace_dep(to_replace, replacement, analyzer, arena);
                cloned.arenaize(analyzer, arena).unwrap();
                *self = cloned;
            }
        }
    }

    pub fn recurse_dearenaize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Self>,
    ) -> Self {
        match self {
            Self::Arena(arena_idx) => arena
                .ranges
                .get(*arena_idx)
                .unwrap()
                .clone()
                .recurse_dearenaize(analyzer, arena),
            Self::Expr(expr) => expr.recurse_dearenaize(analyzer, arena),
            e => e.clone(),
        }
    }

    pub fn dearenaize_clone(&self, arena: &mut RangeArena<Self>) -> Self {
        match self {
            Self::Arena(arena_idx) => arena.ranges.get(*arena_idx).cloned().unwrap_or_default(),
            _ => unreachable!(),
        }
    }

    pub fn dearenaize(&self, arena: &mut RangeArena<Self>) -> (Self, usize) {
        match self {
            Self::Arena(arena_idx) => {
                (
                    arena.take_nonnull(*arena_idx).unwrap_or_default(),
                    // arena.ranges.get(*arena_idx).cloned().unwrap_or_default(),
                    *arena_idx,
                )
            }
            _ => unreachable!(),
        }
    }

    pub fn rearenaize(&self, elem: Self, idx: usize, arena: &mut RangeArena<Self>) {
        if !matches!(elem, Elem::Null) {
            if let Some(t) = arena.ranges.get_mut(idx) {
                *t = elem;
            }
        }
    }

    pub fn arena_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => a == b,
            (Self::Concrete(a), Self::Concrete(b)) => a == b,
            (Self::ConcreteDyn(a), Self::ConcreteDyn(b)) => {
                a.len == b.len
                    && a.val.len() == b.val.len()
                    && a.val
                        .iter()
                        .zip(b.val.iter())
                        .all(|((a, op_a), (b, op_b))| a.arena_eq(b) && op_a == op_b)
            }
            (Self::Reference(a), Self::Reference(b)) => a == b,
            (Self::Expr(a), Self::Expr(b)) => {
                a.lhs.arena_eq(&b.lhs) && a.rhs.arena_eq(&b.rhs) && a.op == b.op
            }
            (Elem::Null, Elem::Null) => true,
            _ => false,
        }
    }
    pub fn as_bytes(
        &self,
        analyzer: &impl GraphBackend,
        maximize: bool,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Vec<u8>> {
        let evaled = if maximize {
            self.maximize(analyzer, arena).ok()?
        } else {
            self.minimize(analyzer, arena).ok()?
        };

        match evaled {
            Elem::Concrete(c) => c.as_bytes(analyzer, maximize, arena),
            Elem::ConcreteDyn(c) => c.as_bytes(analyzer, maximize, arena),
            _ => None,
        }
    }

    pub fn overlaps(
        &self,
        other: &Self,
        eval: bool,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<bool>, GraphError> {
        match (self, other) {
            (Elem::Concrete(s), Elem::Concrete(o)) => Ok(Some(o.val == s.val)),
            (Elem::Reference(s), Elem::Reference(o)) => {
                if s == o {
                    Ok(Some(true))
                } else if eval {
                    let lhs_min = s.minimize(analyzer, arena)?;
                    let rhs_max = o.maximize(analyzer, arena)?;

                    match lhs_min.range_ord(&rhs_max, arena) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = s.maximize(analyzer, arena)?;
                            let rhs_min = o.minimize(analyzer, arena)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(&rhs_min, arena),
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
            (Elem::Reference(s), c @ Elem::Concrete(_)) => {
                if eval {
                    let lhs_min = s.minimize(analyzer, arena)?;

                    match lhs_min.range_ord(c, arena) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = s.maximize(analyzer, arena)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(c, arena),
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
            (Elem::Concrete(_), Elem::Reference(_)) => other.overlaps(self, eval, analyzer, arena),
            _ => Ok(None),
        }
    }

    /// Given an element and a min and max, checks if the element could be equal to the RHS
    pub fn overlaps_dual(
        &self,
        rhs_min: &Self,
        rhs_max: &Self,
        eval: bool,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<bool>, GraphError> {
        match self {
            Self::Reference(d) => {
                if eval {
                    let lhs_min = d.minimize(analyzer, arena)?;
                    let rhs_max = rhs_max.maximize(analyzer, arena)?;

                    match lhs_min.range_ord(&rhs_max, arena) {
                        Some(std::cmp::Ordering::Less) => {
                            // we know our min is less than the other max
                            // check that the max is greater than or eq their min
                            let lhs_max = d.maximize(analyzer, arena)?;
                            let rhs_min = rhs_min.minimize(analyzer, arena)?;
                            Ok(Some(matches!(
                                lhs_max.range_ord(&rhs_min, arena),
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
            Self::Concrete(_) => {
                let (min, max) = if eval {
                    (
                        rhs_min.minimize(analyzer, arena)?,
                        rhs_max.maximize(analyzer, arena)?,
                    )
                } else {
                    (rhs_min.clone(), rhs_max.clone())
                };

                match min.range_ord(self, arena) {
                    Some(std::cmp::Ordering::Less) => Ok(Some(matches!(
                        max.range_ord(self, arena),
                        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                    ))),
                    Some(std::cmp::Ordering::Equal) => Ok(Some(true)),
                    _ => Ok(Some(false)),
                }
            }
            _ => Ok(None),
        }
    }
    pub fn is_negative(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let res = match self {
            Elem::Concrete(RangeConcrete {
                val: Concrete::Int(_, val),
                ..
            }) if val < &I256::zero() => true,
            Elem::Reference(dy) => {
                if maximize {
                    dy.maximize(analyzer, arena)?
                        .is_negative(maximize, analyzer, arena)?
                } else {
                    dy.minimize(analyzer, arena)?
                        .is_negative(maximize, analyzer, arena)?
                }
            }
            Elem::Expr(expr) => {
                if maximize {
                    expr.maximize(analyzer, arena)?
                        .is_negative(maximize, analyzer, arena)?
                } else {
                    expr.minimize(analyzer, arena)?
                        .is_negative(maximize, analyzer, arena)?
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

    pub fn arenaized_flattened(
        &self,
        max: bool,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Box<Elem<Concrete>>> {
        if let Some(idx) = arena.idx(self) {
            if let Some(t) = arena.ranges.get(idx) {
                match t {
                    Elem::Expr(ref arenaized) => {
                        if max {
                            arenaized.flattened_max.clone()
                        } else {
                            arenaized.flattened_min.clone()
                        }
                    }
                    Elem::Reference(ref arenaized) => {
                        if max {
                            arenaized.flattened_max.clone()
                        } else {
                            arenaized.flattened_min.clone()
                        }
                    }
                    Elem::ConcreteDyn(ref arenaized) => {
                        if max {
                            arenaized.flattened_max.clone()
                        } else {
                            arenaized.flattened_min.clone()
                        }
                    }
                    c @ Elem::Concrete(_) => Some(Box::new(c.clone())),
                    c @ Elem::Null => Some(Box::new(c.clone())),
                    Elem::Arena(idx) => Elem::Arena(*idx).arenaized_flattened(max, analyzer, arena),
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn set_arenaized_flattened(
        &self,
        max: bool,
        elem: &Elem<Concrete>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        if let Some(idx) = arena.idx(self) {
            if let Some(ref mut t) = arena.ranges.get_mut(idx) {
                match &mut *t {
                    Elem::Expr(ref mut arenaized) => {
                        if max {
                            arenaized.flattened_max = Some(Box::new(elem.clone()));
                        } else {
                            arenaized.flattened_min = Some(Box::new(elem.clone()));
                        }
                    }
                    Elem::Reference(ref mut arenaized) => {
                        if max {
                            arenaized.flattened_max = Some(Box::new(elem.clone()));
                        } else {
                            arenaized.flattened_min = Some(Box::new(elem.clone()));
                        }
                    }
                    Elem::ConcreteDyn(ref mut arenaized) => {
                        if max {
                            arenaized.flattened_max = Some(Box::new(elem.clone()));
                        } else {
                            arenaized.flattened_min = Some(Box::new(elem.clone()));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    pub fn set_arenaized_cache(
        &self,
        max: bool,
        elem: &Elem<Concrete>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        if let Some(idx) = arena.idx(self) {
            if let Some(t) = arena.ranges.get_mut(idx) {
                match &mut *t {
                    Elem::Expr(ref mut arenaized) => {
                        if max {
                            arenaized.maximized = Some(MinMaxed::Maximized(Box::new(elem.clone())));
                        } else {
                            arenaized.minimized = Some(MinMaxed::Minimized(Box::new(elem.clone())));
                        }
                    }
                    Elem::Reference(ref mut arenaized) => {
                        if max {
                            arenaized.maximized = Some(MinMaxed::Maximized(Box::new(elem.clone())));
                        } else {
                            arenaized.minimized = Some(MinMaxed::Minimized(Box::new(elem.clone())));
                        }
                    }
                    Elem::ConcreteDyn(ref mut arenaized) => {
                        if max {
                            arenaized.maximized = Some(MinMaxed::Maximized(Box::new(elem.clone())));
                        } else {
                            arenaized.minimized = Some(MinMaxed::Minimized(Box::new(elem.clone())));
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    pub fn is_bytes(&self) -> bool {
        matches!(
            self,
            Elem::Concrete(RangeConcrete {
                val: Concrete::Bytes(..),
                ..
            })
        )
    }

    pub fn is_string(&self) -> bool {
        matches!(
            self,
            Elem::Concrete(RangeConcrete {
                val: Concrete::String(..),
                ..
            })
        )
    }

    pub fn is_uint(&self) -> bool {
        matches!(
            self,
            Elem::Concrete(RangeConcrete {
                val: Concrete::Uint(..),
                ..
            })
        )
    }

    pub fn is_int(&self) -> bool {
        matches!(
            self,
            Elem::Concrete(RangeConcrete {
                val: Concrete::Int(..),
                ..
            })
        )
    }
}
