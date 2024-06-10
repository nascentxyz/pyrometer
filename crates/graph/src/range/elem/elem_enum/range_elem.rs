use crate::elem::MinMaxed;
use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{collapse, Elem, MaybeCollapsed, RangeElem},
    GraphBackend, GraphError,
};

use shared::NodeIdx;
use tracing::instrument;

impl RangeElem<Concrete> for Elem<Concrete> {
    type GraphError = GraphError;

    fn arenaize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        match self {
            Self::Arena(_) => return Ok(()),
            Self::Reference(d) => d.arenaize(analyzer)?,
            Self::ConcreteDyn(d) => d.arenaize(analyzer)?,
            Self::Expr(expr) => {
                expr.arenaize(analyzer)?;
            }
            Self::Concrete(c) => c.arenaize(analyzer)?,
            Self::Null => {}
        }

        let self_take = std::mem::take(self);
        *self = Elem::Arena(analyzer.range_arena_idx_or_upsert(self_take));
        Ok(())
    }

    fn range_eq(&self, other: &Self, analyzer: &impl GraphBackend) -> bool {
        match (self, other) {
            (Self::Arena(a), Self::Arena(b)) => a == b,
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
                    self.dearenaize(analyzer)
                        .borrow()
                        .range_ord(&other.dearenaize(analyzer).borrow(), analyzer)
                }
            }
            (Self::Concrete(a), Self::Concrete(b)) => a.range_ord(b, analyzer),
            (Self::Reference(a), Self::Reference(b)) => a.range_ord(b, analyzer),
            (Elem::Null, Elem::Null) => None,
            (_a, Elem::Null) => Some(std::cmp::Ordering::Greater),
            (Elem::Null, _a) => Some(std::cmp::Ordering::Less),
            _ => None,
        }
    }

    #[instrument(level = "trace", skip_all)]
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
            Self::Arena(_) => {
                let de = self.dearenaize(analyzer);
                let res = de.borrow().clone().flatten(maximize, analyzer)?;
                // match &mut *de.borrow_mut() {
                //     Self::Reference(ref mut d) => {
                //         if maximize {
                //             d.flattened_max = Some(Box::new(res));
                //         } else {
                //             d.flattened_min = Some(Box::new(res));
                //         }
                //     }
                //     Self::Expr(ref mut expr) => {
                //         if maximize {
                //             expr.flattened_max = Some(Box::new(res));
                //         } else {
                //             expr.flattened_min = Some(Box::new(res));
                //         }
                //     }
                //     Self::ConcreteDyn(ref mut d) => {
                //         if maximize {
                //             d.flattened_max = Some(Box::new(res));
                //         } else {
                //             d.flattened_min = Some(Box::new(res));
                //         }
                //     }
                //     _ => {}
                // }
                Ok(res)
            }
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn cache_flatten(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        if self.is_flatten_cached(analyzer) {
            return Ok(());
        }

        match self {
            Self::Reference(d) => d.cache_flatten(analyzer),
            Self::Concrete(c) => c.cache_flatten(analyzer),
            Self::Expr(expr) => expr.cache_flatten(analyzer),
            Self::ConcreteDyn(d) => d.cache_flatten(analyzer),
            Self::Null => Ok(()),
            Self::Arena(idx) => {
                tracing::trace!("flattening for arena idx: {idx}");
                let dearenaized = self.dearenaize(analyzer);
                let Ok(mut t) = dearenaized.try_borrow_mut() else {
                    return Ok(());
                };

                t.cache_flatten(analyzer)?;
                Ok(())
            }
        }
    }

    #[instrument(level = "trace", skip_all)]
    fn is_flatten_cached(&self, analyzer: &impl GraphBackend) -> bool {
        match self {
            Self::Reference(d) => d.is_flatten_cached(analyzer),
            Self::Concrete(c) => c.is_flatten_cached(analyzer),
            Self::Expr(expr) => expr.is_flatten_cached(analyzer),
            Self::ConcreteDyn(d) => d.is_flatten_cached(analyzer),
            Self::Null => true,
            Self::Arena(_idx) => {
                if let Ok(t) = self.dearenaize(analyzer).try_borrow() {
                    t.is_flatten_cached(analyzer)
                } else {
                    false
                }
            }
        }
    }

    fn is_min_max_cached(&self, analyzer: &impl GraphBackend) -> (bool, bool) {
        match self {
            Self::Reference(d) => d.is_min_max_cached(analyzer),
            Self::Concrete(_c) => (true, true),
            Self::Expr(expr) => expr.is_min_max_cached(analyzer),
            Self::ConcreteDyn(d) => d.is_min_max_cached(analyzer),
            Self::Null => (true, true),
            Self::Arena(_) => {
                if let Ok(t) = self.dearenaize(analyzer).try_borrow() {
                    t.is_min_max_cached(analyzer)
                } else {
                    (false, false)
                }
            }
        }
    }

    fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        match self {
            Self::Reference(d) => d.dependent_on(analyzer),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(analyzer),
            Self::ConcreteDyn(d) => d.dependent_on(analyzer),
            Self::Null => vec![],
            Self::Arena(_) => {
                if let Ok(t) = self.dearenaize(analyzer).try_borrow() {
                    t.dependent_on(analyzer)
                } else {
                    vec![]
                }
            }
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
            Self::Arena(_) => self
                .dearenaize(analyzer)
                .borrow()
                .recursive_dependent_on(analyzer),
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
            Self::Arena(_) => self.dearenaize(analyzer).borrow().has_cycle(seen, analyzer),
        }
    }

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, Self::GraphError> {
        match self {
            Self::Reference(d) => d.depends_on(var, seen, analyzer),
            Self::Concrete(_) => Ok(false),
            Self::Expr(expr) => expr.depends_on(var, seen, analyzer),
            Self::ConcreteDyn(d) => d.depends_on(var, seen, analyzer),
            Self::Null => Ok(false),
            Self::Arena(_) => self
                .dearenaize(analyzer)
                .borrow()
                .depends_on(var, seen, analyzer),
        }
    }

    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
    ) {
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
            Self::Arena(_idx) => {
                let dearenaized = self.dearenaize(analyzer);
                dearenaized
                    .borrow_mut()
                    .filter_recursion(node_idx, new_idx, analyzer);
            }
        }
    }

    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(idx) = analyzer.range_arena_idx(self) {
            let (_min, max) = Elem::Arena(idx).is_min_max_cached(analyzer);
            if max {
                tracing::trace!("maximize cache hit");
                if let Ok(b) = analyzer.range_arena().ranges[idx].try_borrow() {
                    match &*b {
                        Reference(dy) => return dy.maximize(analyzer),
                        Concrete(inner) => return inner.maximize(analyzer),
                        ConcreteDyn(inner) => return inner.maximize(analyzer),
                        Expr(expr) => return expr.maximize(analyzer),
                        Null => return Ok(Elem::Null),
                        _ => {}
                    }
                }
            }
        }

        use Elem::*;
        let res = match self {
            Reference(dy) => dy.maximize(analyzer)?,
            Concrete(inner) => inner.maximize(analyzer)?,
            ConcreteDyn(inner) => inner.maximize(analyzer)?,
            Expr(expr) => expr.maximize(analyzer)?,
            Null => Elem::Null,
            Arena(_) => {
                let dearenaized = self.dearenaize(analyzer);
                let res = {
                    let Ok(t) = dearenaized.try_borrow() else {
                        return Ok(self.clone());
                    };
                    t.maximize(analyzer)?
                };

                if let Ok(mut b) = dearenaized.try_borrow_mut() {
                    match &mut *b {
                        Self::Reference(ref mut d) => {
                            tracing::trace!("maximize cache MISS: {self}");
                            d.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                        Self::Expr(ref mut expr) => {
                            tracing::trace!("maximize cache MISS: {self}");
                            expr.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                        Self::ConcreteDyn(ref mut d) => {
                            tracing::trace!("maximize cache MISS: {self}");
                            d.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                        }
                        _ => {}
                    }
                }

                let (_min, max) = self.is_min_max_cached(analyzer);
                assert!(max, "????");

                res
            }
        };
        Ok(res)
    }

    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;

        if let Some(idx) = analyzer.range_arena_idx(self) {
            let (min, _max) = Elem::Arena(idx).is_min_max_cached(analyzer);
            if min {
                tracing::trace!("minimize cache hit");
                if let Ok(b) = analyzer.range_arena().ranges[idx].try_borrow() {
                    match &*b {
                        Reference(dy) => return dy.minimize(analyzer),
                        Concrete(inner) => return inner.minimize(analyzer),
                        ConcreteDyn(inner) => return inner.minimize(analyzer),
                        Expr(expr) => return expr.minimize(analyzer),
                        Null => return Ok(Elem::Null),
                        _ => {}
                    }
                }
            }
        }

        let res = match self {
            Reference(dy) => dy.minimize(analyzer)?,
            Concrete(inner) => inner.minimize(analyzer)?,
            ConcreteDyn(inner) => inner.minimize(analyzer)?,
            Expr(expr) => expr.minimize(analyzer)?,
            Null => Elem::Null,
            Arena(_) => {
                let dearenaized = self.dearenaize(analyzer);
                let res = {
                    let Ok(t) = dearenaized.try_borrow() else {
                        return Ok(self.clone());
                    };
                    t.minimize(analyzer)?
                };

                if let Ok(mut b) = dearenaized.try_borrow_mut() {
                    match &mut *b {
                        Self::Reference(ref mut d) => {
                            tracing::trace!("minimize cache MISS: {self}");
                            d.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                        Self::Expr(ref mut expr) => {
                            tracing::trace!("minimize cache MISS: {self}");
                            expr.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                        Self::ConcreteDyn(ref mut d) => {
                            tracing::trace!("minimize cache MISS: {self}");
                            d.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                        }
                        _ => {}
                    }
                }

                let (min, _max) = self.is_min_max_cached(analyzer);
                assert!(min, "????");
                res
            }
        };
        Ok(res)
    }

    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;

        if let Some(idx) = analyzer.range_arena_idx(self) {
            if let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() {
                match &*t {
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
                    Null => return Ok(Elem::Null),
                    _ => {}
                }
            }
        }

        match self {
            Reference(dy) => dy.simplify_maximize(analyzer),
            Concrete(inner) => inner.simplify_maximize(analyzer),
            ConcreteDyn(inner) => inner.simplify_maximize(analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    let res = collapsed.simplify_maximize(analyzer)?;
                    collapsed.set_arenaized_flattened(true, &res, analyzer);
                    Ok(res)
                }
                _ => {
                    let res = expr.simplify_maximize(analyzer)?;
                    expr.set_arenaized_flattened(true, res.clone(), analyzer);
                    Ok(res)
                }
            },
            Null => Ok(Elem::Null),
            Arena(_) => {
                let dearenaized = self.dearenaize(analyzer);
                let flat = (*dearenaized.borrow()).clone().flatten(true, analyzer)?;
                let max = flat.simplify_maximize(analyzer)?;
                // let min = flat.simplify_minimize(analyzer)?;
                if let Ok(mut b) = dearenaized.try_borrow_mut() {
                    match &mut *b {
                        Self::Reference(ref mut d) => {
                            tracing::trace!("simplify maximize cache MISS: {self}");
                            d.flattened_max = Some(Box::new(max.clone()));
                            // d.flattened_min = Some(Box::new(min.clone()));
                        }
                        Self::Expr(ref mut expr) => {
                            tracing::trace!("simplify maximize cache MISS: {self}");
                            expr.flattened_max = Some(Box::new(max.clone()));
                            // expr.flattened_min = Some(Box::new(min.clone()));
                        }
                        Self::ConcreteDyn(ref mut d) => {
                            tracing::trace!("simplify maximize cache MISS: {self}");
                            d.flattened_max = Some(Box::new(max.clone()));
                            // d.flattened_min = Some(Box::new(min.clone()));
                        }
                        _ => {}
                    }
                }

                // assert!(self.is_flatten_cached(analyzer), "????");
                Ok(max)
            }
        }
    }

    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;

        if let Some(idx) = analyzer.range_arena_idx(self) {
            if let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() {
                match &*t {
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
                    Null => return Ok(Elem::Null),
                    _ => {}
                }
            }
        }

        let res = match self {
            Reference(dy) => dy.simplify_minimize(analyzer),
            Concrete(inner) => inner.simplify_minimize(analyzer),
            ConcreteDyn(inner) => inner.simplify_minimize(analyzer),
            Expr(expr) => match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                MaybeCollapsed::Collapsed(collapsed) => {
                    let res = collapsed.simplify_minimize(analyzer)?;
                    collapsed.set_arenaized_flattened(false, &res, analyzer);
                    Ok(res)
                }
                _ => {
                    let res = expr.simplify_minimize(analyzer)?;
                    expr.set_arenaized_flattened(false, res.clone(), analyzer);
                    Ok(res)
                }
            },
            Null => Ok(Elem::Null),
            Arena(_) => {
                let dearenaized = self.dearenaize(analyzer);
                let flat = (*dearenaized.borrow()).clone().flatten(false, analyzer)?;
                let min = flat.simplify_minimize(analyzer)?;
                if let Ok(mut b) = dearenaized.try_borrow_mut() {
                    match &mut *b {
                        Self::Reference(ref mut d) => {
                            tracing::trace!("simplify minimize cache MISS: {self}");
                            d.flattened_min = Some(Box::new(min.clone()));
                        }
                        Self::Expr(ref mut expr) => {
                            tracing::trace!("simplify minimize cache MISS: {self}");
                            expr.flattened_min = Some(Box::new(min.clone()));
                        }
                        Self::ConcreteDyn(ref mut d) => {
                            tracing::trace!("simplify minimize cache MISS: {self}");
                            d.flattened_min = Some(Box::new(min.clone()));
                        }
                        _ => {}
                    }
                }

                Ok(min)
            }
        }?;

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
                    collapsed.cache_maximize(analyzer)?;
                    let max = collapsed.maximize(analyzer)?;
                    self.set_arenaized_flattened(true, &max, analyzer);
                    *self = collapsed;
                    Ok(())
                }
                _ => {
                    expr.cache_maximize(analyzer)?;
                    let max = expr.maximize(analyzer)?;
                    self.set_arenaized_flattened(true, &max, analyzer);
                    Ok(())
                }
            },
            Null => Ok(()),
            Arena(_idx) => {
                let dearenaized = self.dearenaize(analyzer);
                if let Ok(mut t) = dearenaized.try_borrow_mut() {
                    t.cache_maximize(analyzer)?;
                }

                Ok(())
            }
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
                    let min = collapsed.minimize(analyzer)?;
                    self.set_arenaized_flattened(false, &min, analyzer);
                    *self = collapsed;
                    Ok(())
                }
                _ => {
                    expr.cache_minimize(analyzer)?;
                    let min = expr.minimize(analyzer)?;
                    self.set_arenaized_flattened(false, &min, analyzer);
                    Ok(())
                }
            },
            Null => Ok(()),
            Arena(_idx) => {
                let dearenaized = self.dearenaize(analyzer);
                if let Ok(mut t) = dearenaized.try_borrow_mut() {
                    t.cache_minimize(analyzer)?;
                }

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
