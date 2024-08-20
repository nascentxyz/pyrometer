use crate::elem::{MinMaxed, RangeArenaLike};
use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{collapse, Elem, MaybeCollapsed, RangeElem},
    GraphBackend,
};

use shared::{GraphError, NodeIdx, RangeArena};

impl RangeElem<Concrete> for Elem<Concrete> {
    type GraphError = GraphError;

    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        match self {
            Self::Arena(_) => return Ok(()),
            Self::Reference(d) => d.arenaize(analyzer, arena)?,
            Self::ConcreteDyn(d) => d.arenaize(analyzer, arena)?,
            Self::Expr(expr) => {
                expr.arenaize(analyzer, arena)?;
            }
            Self::Concrete(c) => c.arenaize(analyzer, arena)?,
            Self::Null => {}
        }

        let self_take = std::mem::take(self);
        *self = Elem::Arena(arena.idx_or_upsert(self_take, analyzer));
        Ok(())
    }

    fn range_eq(&self, other: &Self, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => a == b,
            (Self::Concrete(a), Self::Concrete(b)) => a.range_eq(b, arena),
            (Self::ConcreteDyn(a), Self::ConcreteDyn(b)) => a.range_eq(b, arena),
            (Self::Reference(a), Self::Reference(b)) => a.idx == b.idx,
            _ => false,
        }
    }

    fn range_ord(
        &self,
        other: &Self,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => {
                if a == b {
                    Some(std::cmp::Ordering::Equal)
                } else {
                    let (l, a) = self.dearenaize(arena);
                    let (r, b) = other.dearenaize(arena);
                    let res = l.range_ord(&r, arena);
                    self.rearenaize(l, a, arena);
                    self.rearenaize(r, b, arena);
                    res
                }
            }
            (Self::Arena(_), _) => {
                let (l, a) = self.dearenaize(arena);
                let res = l.range_ord(other, arena);
                self.rearenaize(l, a, arena);
                res
            }
            (_, Self::Arena(_)) => {
                let (r, b) = other.dearenaize(arena);
                let res = self.range_ord(&r, arena);
                self.rearenaize(r, b, arena);
                res
            }
            (Self::Concrete(a), Self::Concrete(b)) => a.range_ord(b, arena),
            (c @ Self::Concrete(_), Self::Reference(r)) => {
                if let (Some(MinMaxed::Minimized(min)), Some(MinMaxed::Maximized(max))) =
                    (&r.minimized, &r.maximized)
                {
                    let min_ord = c.range_ord(min, arena)?;
                    let max_ord = c.range_ord(max, arena)?;
                    if min_ord == max_ord {
                        Some(min_ord)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            (Self::Reference(r), c @ Self::Concrete(_)) => {
                if let (Some(MinMaxed::Minimized(min)), Some(MinMaxed::Maximized(max))) =
                    (&r.minimized, &r.maximized)
                {
                    let min_ord = min.range_ord(c, arena)?;
                    let max_ord = max.range_ord(c, arena)?;
                    if min_ord == max_ord {
                        Some(min_ord)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            (Self::Reference(a), Self::Reference(b)) => a.range_ord(b, arena),
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
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        match self {
            Self::Reference(d) => d.flatten(maximize, analyzer, arena),
            Self::Concrete(c) => c.flatten(maximize, analyzer, arena),
            Self::Expr(expr) => expr.flatten(maximize, analyzer, arena),
            Self::ConcreteDyn(d) => d.flatten(maximize, analyzer, arena),
            Self::Null => Ok(Elem::Null),
            Self::Arena(_) => {
                let (de, idx) = self.dearenaize(arena);
                let res = de.flatten(maximize, analyzer, arena)?;
                self.rearenaize(de, idx, arena);
                Ok(res)
            }
        }
    }

    fn cache_flatten(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        if self.is_flatten_cached(analyzer, arena) {
            return Ok(());
        }

        match self {
            Self::Reference(d) => d.cache_flatten(analyzer, arena),
            Self::Concrete(c) => c.cache_flatten(analyzer, arena),
            Self::Expr(expr) => expr.cache_flatten(analyzer, arena),
            Self::ConcreteDyn(d) => d.cache_flatten(analyzer, arena),
            Self::Null => Ok(()),
            Self::Arena(idx) => {
                tracing::trace!("flattening for arena idx: {idx}");
                let (mut dearenaized, idx) = self.dearenaize(arena);
                dearenaized.cache_flatten(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);
                Ok(())
            }
        }
    }

    fn is_flatten_cached(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        match self {
            Self::Reference(d) => d.is_flatten_cached(analyzer, arena),
            Self::Concrete(c) => c.is_flatten_cached(analyzer, arena),
            Self::Expr(expr) => expr.is_flatten_cached(analyzer, arena),
            Self::ConcreteDyn(d) => d.is_flatten_cached(analyzer, arena),
            Self::Null => true,
            Self::Arena(_) => {
                let (t, idx) = self.dearenaize(arena);
                let res = t.is_flatten_cached(analyzer, arena);
                self.rearenaize(t, idx, arena);
                res
            }
        }
    }

    fn is_min_max_cached(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (bool, bool) {
        match self {
            Self::Reference(d) => d.is_min_max_cached(analyzer, arena),
            Self::Concrete(_c) => (true, true),
            Self::Expr(expr) => expr.is_min_max_cached(analyzer, arena),
            Self::ConcreteDyn(d) => d.is_min_max_cached(analyzer, arena),
            Self::Null => (true, true),
            Self::Arena(_) => {
                let (t, idx) = self.dearenaize(arena);
                let res = t.is_min_max_cached(analyzer, arena);
                self.rearenaize(t, idx, arena);
                res
            }
        }
    }

    fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        match self {
            Self::Reference(d) => d.dependent_on(analyzer, arena),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(analyzer, arena),
            Self::ConcreteDyn(d) => d.dependent_on(analyzer, arena),
            Self::Null => vec![],
            Self::Arena(_) => {
                let (t, idx) = self.dearenaize(arena);
                let res = t.dependent_on(analyzer, arena);
                self.rearenaize(t, idx, arena);
                res
            }
        }
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        match self {
            Self::Reference(d) => d.recursive_dependent_on(analyzer, arena),
            Self::Concrete(_) => Ok(vec![]),
            Self::Expr(expr) => expr.recursive_dependent_on(analyzer, arena),
            Self::ConcreteDyn(d) => d.recursive_dependent_on(analyzer, arena),
            Self::Null => Ok(vec![]),
            Self::Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let res = dearenaized.recursive_dependent_on(analyzer, arena);
                self.rearenaize(dearenaized, idx, arena);
                res
            }
        }
    }

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, Self::GraphError> {
        match self {
            Self::Reference(d) => d.has_cycle(seen, analyzer, arena),
            Self::Concrete(_) => Ok(false),
            Self::Expr(expr) => expr.has_cycle(seen, analyzer, arena),
            Self::ConcreteDyn(d) => d.has_cycle(seen, analyzer, arena),
            Self::Null => Ok(false),
            Self::Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let res = dearenaized.has_cycle(seen, analyzer, arena);
                self.rearenaize(dearenaized, idx, arena);
                res
            }
        }
    }

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, Self::GraphError> {
        match self {
            Self::Reference(d) => d.depends_on(var, seen, analyzer, arena),
            Self::Concrete(_) => Ok(false),
            Self::Expr(expr) => expr.depends_on(var, seen, analyzer, arena),
            Self::ConcreteDyn(d) => d.depends_on(var, seen, analyzer, arena),
            Self::Null => Ok(false),
            Self::Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let res = dearenaized.depends_on(var, seen, analyzer, arena);
                self.rearenaize(dearenaized, idx, arena);
                res
            }
        }
    }

    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        match self {
            Self::Reference(ref mut d) => {
                if d.idx == node_idx {
                    d.idx = new_idx
                }
            }
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.filter_recursion(node_idx, new_idx, analyzer, arena),
            Self::ConcreteDyn(d) => d.filter_recursion(node_idx, new_idx, analyzer, arena),
            Self::Null => {}
            Self::Arena(_) => {
                let (mut dearenaized, idx) = self.dearenaize(arena);
                dearenaized.filter_recursion(node_idx, new_idx, analyzer, arena);
                self.rearenaize(dearenaized, idx, arena);
            }
        }
    }

    fn maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.maximize(analyzer, arena)?,
            Concrete(inner) => inner.maximize(analyzer, arena)?,
            ConcreteDyn(inner) => inner.maximize(analyzer, arena)?,
            Expr(expr) => expr.maximize(analyzer, arena)?,
            Null => Elem::Null,
            Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let res = dearenaized.maximize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);

                match arena.ranges.get_mut(idx) {
                    Some(Self::Reference(ref mut d)) => {
                        if d.maximized.is_none() {
                            d.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                    }
                    Some(Self::Expr(ref mut expr)) => {
                        if expr.maximized.is_none() {
                            expr.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                    }
                    Some(Self::ConcreteDyn(ref mut d)) => {
                        if d.maximized.is_none() {
                            d.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                    }
                    _ => {}
                }

                let (_min, max) = self.is_min_max_cached(analyzer, arena);
                assert!(max, "????");

                res
            }
        };
        Ok(res)
    }

    fn minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.minimize(analyzer, arena)?,
            Concrete(inner) => inner.minimize(analyzer, arena)?,
            ConcreteDyn(inner) => inner.minimize(analyzer, arena)?,
            Expr(expr) => expr.minimize(analyzer, arena)?,
            Null => Elem::Null,
            Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let res = dearenaized.minimize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);

                match arena.ranges.get_mut(idx) {
                    Some(Self::Reference(ref mut d)) => {
                        if d.minimized.is_none() {
                            d.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                    }
                    Some(Self::Expr(ref mut expr)) => {
                        if expr.minimized.is_none() {
                            expr.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                    }
                    Some(Self::ConcreteDyn(ref mut d)) => {
                        if d.minimized.is_none() {
                            d.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                    }
                    _ => {}
                }

                let (min, _max) = self.is_min_max_cached(analyzer, arena);
                assert!(min, "????");
                res
            }
        };
        Ok(res)
    }

    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;

        if let Some(idx) = arena.idx(self) {
            if let Some(t) = arena.ranges.get(idx) {
                match t {
                    Reference(dy) => {
                        if let Some(max) = &dy.flattened_max {
                            return Ok(*max.clone());
                        }
                    }
                    c @ Concrete(_) => return Ok(c.clone()),
                    ConcreteDyn(inner) => {
                        if let Some(max) = &inner.flattened_max {
                            return Ok(*max.clone());
                        }
                    }
                    Expr(expr) => {
                        if let Some(max) = &expr.flattened_max {
                            return Ok(*max.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        match self {
            Reference(dy) => dy.simplify_maximize(analyzer, arena),
            Concrete(inner) => inner.simplify_maximize(analyzer, arena),
            ConcreteDyn(inner) => inner.simplify_maximize(analyzer, arena),
            Expr(expr) => match collapse(*expr.lhs.clone(), expr.op, *expr.rhs.clone(), arena) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    let res = collapsed.simplify_maximize(analyzer, arena)?;
                    collapsed.set_arenaized_flattened(true, &res, arena);
                    Ok(res)
                }
                _ => {
                    let res = expr.simplify_maximize(analyzer, arena)?;
                    expr.set_arenaized_flattened(true, res.clone(), arena);
                    Ok(res)
                }
            },
            Null => Ok(Elem::Null),
            Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let flat = dearenaized.flatten(true, analyzer, arena)?;
                let max = flat.simplify_maximize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);

                match arena.ranges.get_mut(idx) {
                    Some(Self::Reference(ref mut d)) => {
                        tracing::trace!("simplify maximize cache MISS: {self}");
                        d.flattened_max = Some(Box::new(max.clone()));
                    }
                    Some(Self::Expr(ref mut expr)) => {
                        tracing::trace!("simplify maximize cache MISS: {self}");
                        expr.flattened_max = Some(Box::new(max.clone()));
                    }
                    Some(Self::ConcreteDyn(ref mut d)) => {
                        tracing::trace!("simplify maximize cache MISS: {self}");
                        d.flattened_max = Some(Box::new(max.clone()));
                    }
                    _ => {}
                }

                Ok(max)
            }
        }
    }

    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;

        if let Some(idx) = arena.idx(self) {
            if let Some(t) = arena.ranges.get(idx) {
                match t {
                    Reference(dy) => {
                        if let Some(min) = &dy.flattened_min {
                            return Ok(*min.clone());
                        }
                    }
                    c @ Concrete(_) => return Ok(c.clone()),
                    ConcreteDyn(inner) => {
                        if let Some(min) = &inner.flattened_min {
                            return Ok(*min.clone());
                        }
                    }
                    Expr(expr) => {
                        if let Some(min) = &expr.flattened_min {
                            return Ok(*min.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        let res = match self {
            Reference(dy) => dy.simplify_minimize(analyzer, arena),
            Concrete(inner) => inner.simplify_minimize(analyzer, arena),
            ConcreteDyn(inner) => inner.simplify_minimize(analyzer, arena),
            Expr(expr) => match collapse(*expr.lhs.clone(), expr.op, *expr.rhs.clone(), arena) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    let res = collapsed.simplify_minimize(analyzer, arena)?;
                    collapsed.set_arenaized_flattened(false, &res, arena);
                    Ok(res)
                }
                _ => {
                    let res = expr.simplify_minimize(analyzer, arena)?;
                    expr.set_arenaized_flattened(false, res.clone(), arena);
                    Ok(res)
                }
            },
            Null => Ok(Elem::Null),
            Arena(_) => {
                let (dearenaized, idx) = self.dearenaize(arena);
                let flat = dearenaized.flatten(false, analyzer, arena)?;
                let min = flat.simplify_minimize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);

                match arena.ranges.get_mut(idx) {
                    Some(Self::Reference(ref mut d)) => {
                        tracing::trace!(
                            "simplify minimize cache MISS: {self}, new simp min: {min}"
                        );
                        d.flattened_min = Some(Box::new(min.clone()));
                    }
                    Some(Self::Expr(ref mut expr)) => {
                        tracing::trace!(
                            "simplify minimize cache MISS: {self}, new simp min: {min}"
                        );
                        expr.flattened_min = Some(Box::new(min.clone()));
                    }
                    Some(Self::ConcreteDyn(ref mut d)) => {
                        tracing::trace!(
                            "simplify minimize cache MISS: {self}, new simp min: {min}"
                        );
                        d.flattened_min = Some(Box::new(min.clone()));
                    }
                    _ => {}
                }

                Ok(min)
            }
        }?;

        Ok(res)
    }

    fn cache_maximize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_maximize(analyzer, arena),
            Concrete(inner) => inner.cache_maximize(analyzer, arena),
            ConcreteDyn(inner) => inner.cache_maximize(analyzer, arena),
            Expr(expr) => match collapse(*expr.lhs.clone(), expr.op, *expr.rhs.clone(), arena) {
                MaybeCollapsed::Collapsed(mut collapsed) => {
                    collapsed.cache_maximize(analyzer, arena)?;
                    let max = collapsed.maximize(analyzer, arena)?;
                    self.set_arenaized_cache(true, &max, arena);
                    *self = collapsed;
                    Ok(())
                }
                _ => {
                    expr.cache_maximize(analyzer, arena)?;
                    let max = expr.maximize(analyzer, arena)?;
                    self.set_arenaized_cache(true, &max, arena);
                    Ok(())
                }
            },
            Null => Ok(()),
            Arena(_) => {
                let (mut dearenaized, idx) = self.dearenaize(arena);
                dearenaized.cache_maximize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);
                Ok(())
            }
        }
    }

    fn cache_minimize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_minimize(analyzer, arena),
            Concrete(inner) => inner.cache_minimize(analyzer, arena),
            ConcreteDyn(inner) => inner.cache_minimize(analyzer, arena),
            Expr(expr) => match collapse(*expr.lhs.clone(), expr.op, *expr.rhs.clone(), arena) {
                MaybeCollapsed::Collapsed(mut collapsed) => {
                    collapsed.cache_minimize(analyzer, arena)?;
                    let min = collapsed.minimize(analyzer, arena)?;
                    self.set_arenaized_cache(false, &min, arena);
                    *self = collapsed;
                    Ok(())
                }
                _ => {
                    expr.cache_minimize(analyzer, arena)?;
                    let min = expr.minimize(analyzer, arena)?;
                    self.set_arenaized_cache(false, &min, arena);
                    Ok(())
                }
            },
            Null => Ok(()),
            Arena(_) => {
                let (mut dearenaized, idx) = self.dearenaize(arena);
                dearenaized.cache_minimize(analyzer, arena)?;
                self.rearenaize(dearenaized, idx, arena);
                Ok(())
            }
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
            Arena(_idx) => {}
        }
    }
}
