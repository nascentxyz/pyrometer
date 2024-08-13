mod collapse;
pub use collapse::*;

mod simplify;

use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{
        elem::{Elem, MinMaxed, RangeArenaLike, RangeConcrete, RangeElem, RangeOp},
        exec_traits::*,
    },
    GraphBackend,
};
use std::hash::Hasher;
use std::{fmt::Display, hash::Hash};

use ethers_core::types::U256;
use shared::{GraphError, NodeIdx, RangeArena};

/// A range expression composed of other range [`Elem`]
#[derive(Clone, Debug, Ord, PartialOrd)]
pub struct RangeExpr<T> {
    pub maximized: Option<MinMaxed<T>>,
    pub minimized: Option<MinMaxed<T>>,
    pub flattened_min: Option<Box<Elem<T>>>,
    pub flattened_max: Option<Box<Elem<T>>>,
    pub lhs: Box<Elem<T>>,
    pub op: RangeOp,
    pub rhs: Box<Elem<T>>,
}

impl std::fmt::Display for RangeExpr<Concrete> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.op {
            RangeOp::Min | RangeOp::Max => {
                write!(f, "{}{{{}, {}}}", self.op, self.lhs, self.rhs)
            }
            RangeOp::Cast => match &*self.rhs {
                Elem::Concrete(RangeConcrete { val, .. }) => {
                    write!(
                        f,
                        "{}({}, {})",
                        self.op,
                        self.lhs,
                        val.as_builtin().basic_as_string()
                    )
                }
                _ => write!(f, "{}({}, {})", self.op, self.lhs, self.rhs),
            },
            RangeOp::BitNot => {
                write!(f, "~{}", self.lhs)
            }
            _ => write!(f, "({} {} {})", self.lhs, self.op, self.rhs),
        }
    }
}

impl<T: std::cmp::PartialEq> PartialEq for RangeExpr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.lhs == other.lhs && self.rhs == other.rhs
    }
}
impl<T: std::cmp::PartialEq> Eq for RangeExpr<T> {}

impl<T: Hash> Hash for RangeExpr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self.lhs).hash(state);
        self.op.hash(state);
        (*self.rhs).hash(state);
    }
}

impl RangeExpr<Concrete> {
    pub fn is_noop(&self) -> (bool, usize) {
        let one = Elem::from(Concrete::from(U256::one()));
        let zero = Elem::from(Concrete::from(U256::zero()));
        match self.op {
            RangeOp::Mul(_) | RangeOp::Div(_) => {
                if *self.lhs == one {
                    (true, 0)
                } else if *self.rhs == one {
                    (true, 1)
                } else {
                    (false, 0)
                }
            }
            RangeOp::Add(_) | RangeOp::Sub(_) => {
                if *self.lhs == zero {
                    (true, 0)
                } else if *self.rhs == zero {
                    (true, 1)
                } else {
                    (false, 0)
                }
            }
            _ => (false, 0),
        }
    }

    pub fn inverse_if_boolean(&self) -> Option<Self> {
        if EQ_OPS.contains(&self.op) {
            if SINGLETON_EQ_OPS.contains(&self.op) {
                let mut new_self = self.clone();
                new_self.uncache();
                new_self.op = new_self.op.logical_inverse()?;
                Some(new_self)
            } else {
                // non-singleton, i.e. AND or OR
                let mut new_self = self.clone();
                new_self.uncache();
                new_self.op = new_self.op.inverse()?;
                if let Some(new_lhs) = new_self.inverse_if_boolean() {
                    *new_self.lhs = Elem::Expr(new_lhs);
                }
                if let Some(new_rhs) = new_self.inverse_if_boolean() {
                    *new_self.rhs = Elem::Expr(new_rhs);
                }
                Some(new_self)
            }
        } else {
            None
        }
    }

    pub fn recurse_dearenaize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Elem<Concrete> {
        Elem::Expr(Self::new(
            self.lhs.recurse_dearenaize(analyzer, arena).clone(),
            self.op,
            self.rhs.recurse_dearenaize(analyzer, arena).clone(),
        ))
    }

    pub fn arena_idx(&self, arena: &RangeArena<Elem<Concrete>>) -> Option<usize> {
        let expr = Elem::Expr(RangeExpr::new(
            Elem::Arena(arena.idx(&self.lhs)?),
            self.op,
            Elem::Arena(arena.idx(&self.rhs)?),
        ));
        arena.idx(&expr)
    }

    pub fn arenaized_cache(
        &self,
        max: bool,
        _analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<MinMaxed<Concrete>> {
        if let Some(idx) = self.arena_idx(arena) {
            let t = arena.ranges.get_mut(idx)?;
            let Elem::Expr(ref mut arenaized) = *t else {
                return None;
            };
            return if max {
                arenaized.maximized.clone()
            } else {
                arenaized.minimized.clone()
            };
        }
        None
    }

    pub fn arenaized_flat_cache(
        &self,
        max: bool,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Box<Elem<Concrete>>> {
        if let Some(idx) = self.arena_idx(arena) {
            let t = arena.ranges.get_mut(idx)?;
            let Elem::Expr(ref mut arenaized) = *t else {
                return None;
            };
            return if max {
                arenaized.flattened_max.clone()
            } else {
                arenaized.flattened_min.clone()
            };
        }
        None
    }

    pub fn set_arenaized_flattened(
        &self,
        max: bool,
        elem: Elem<Concrete>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        if let Some(idx) = self.arena_idx(arena) {
            if let Some(t) = arena.ranges.get_mut(idx) {
                let Elem::Expr(arenaized) = &mut *t else {
                    return;
                };

                if max {
                    arenaized.flattened_max = Some(Box::new(elem));
                } else {
                    arenaized.flattened_min = Some(Box::new(elem));
                }
            }
        }
    }
}

impl<T: Ord> RangeExpr<T> {
    /// Creates a new range expression given a left hand side range [`Elem`], a [`RangeOp`], and a a right hand side range [`Elem`].
    pub fn new(lhs: Elem<T>, op: RangeOp, rhs: Elem<T>) -> RangeExpr<T> {
        RangeExpr {
            maximized: None,
            minimized: None,
            flattened_max: None,
            flattened_min: None,
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        }
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.lhs.contains_node(node_idx) || self.rhs.contains_node(node_idx)
    }
}

impl RangeElem<Concrete> for RangeExpr<Concrete> {
    type GraphError = GraphError;

    // #[tracing::instrument(level = "trace", skip_all)]
    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        if self.arena_idx(arena).is_none() {
            let lhs = std::mem::take(&mut self.lhs);
            let rhs = std::mem::take(&mut self.rhs);
            self.lhs = Box::new(Elem::Arena(arena.idx_or_upsert(*lhs, analyzer)));
            self.rhs = Box::new(Elem::Arena(arena.idx_or_upsert(*rhs, analyzer)));
            let _ = arena.idx_or_upsert(Elem::Expr(self.clone()), analyzer);
        }
        Ok(())
    }

    fn range_eq(&self, _other: &Self, _arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        false
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        match (maximize, &self.flattened_min, &self.flattened_max) {
            (true, _, Some(flat)) | (false, Some(flat), _) => {
                return Ok(*flat.clone());
            }
            _ => {}
        }

        if let Some(arenaized) = self.arenaized_flat_cache(maximize, arena) {
            return Ok(*arenaized);
        }

        let lhs = self.lhs.flatten(maximize, analyzer, arena)?;
        let rhs = self.rhs.flatten(maximize, analyzer, arena)?;
        Ok(Elem::Expr(RangeExpr::new(lhs, self.op, rhs)))
    }

    fn is_flatten_cached(
        &self,
        _analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some() || {
            if let Some(idx) = self.arena_idx(arena) {
                if let Some(Elem::Expr(ref arenaized)) = arena.ranges.get(idx) {
                    arenaized.flattened_min.is_some() && arenaized.flattened_max.is_some()
                } else {
                    false
                }
            } else {
                false
            }
        }
    }

    fn is_min_max_cached(
        &self,
        _analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (bool, bool) {
        let (arena_cached_min, arena_cached_max) = {
            if let Some(idx) = self.arena_idx(arena) {
                if let Some(Elem::Expr(ref arenaized)) = arena.ranges.get(idx) {
                    (arenaized.minimized.is_some(), arenaized.maximized.is_some())
                } else {
                    (false, false)
                }
            } else {
                (false, false)
            }
        };
        (
            self.minimized.is_some() || arena_cached_min,
            self.maximized.is_some() || arena_cached_max,
        )
    }

    fn range_ord(
        &self,
        _other: &Self,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on(analyzer, arena);
        deps.extend(self.rhs.dependent_on(analyzer, arena));
        deps
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps = self.lhs.recursive_dependent_on(analyzer, arena)?;
        deps.extend(self.rhs.recursive_dependent_on(analyzer, arena)?);
        Ok(deps)
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let lhs_has_cycle = self.lhs.has_cycle(seen, analyzer, arena)?;
        let rhs_has_cycle = self.rhs.has_cycle(seen, analyzer, arena)?;
        Ok(lhs_has_cycle || rhs_has_cycle)
    }

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, Self::GraphError> {
        let lhs_deps_on = self.lhs.depends_on(var, seen, analyzer, arena)?;
        let rhs_deps_on = self.rhs.depends_on(var, seen, analyzer, arena)?;
        Ok(lhs_deps_on || rhs_deps_on)
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.lhs
            .filter_recursion(node_idx, new_idx, analyzer, arena);
        self.rhs
            .filter_recursion(node_idx, new_idx, analyzer, arena);
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            Ok(*cached)
        } else if let Some(MinMaxed::Maximized(cached)) =
            self.arenaized_cache(true, analyzer, arena)
        {
            Ok(*cached)
        } else if self.op == RangeOp::SetIndices {
            self.simplify_exec_op(true, analyzer, arena)
        } else {
            self.exec_op(true, analyzer, arena)
        }
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            Ok(*cached)
        } else if let Some(MinMaxed::Minimized(cached)) =
            self.arenaized_cache(false, analyzer, arena)
        {
            Ok(*cached)
        } else if self.op == RangeOp::SetIndices {
            self.simplify_exec_op(false, analyzer, arena)
        } else {
            self.exec_op(false, analyzer, arena)
        }
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_max) = &self.flattened_max {
            return Ok(*simp_max.clone());
        }

        if let Some(arenaized) = self.arenaized_flat_cache(true, arena) {
            return Ok(*arenaized);
        }

        let l = self.lhs.simplify_maximize(analyzer, arena)?;
        let r = self.rhs.simplify_maximize(analyzer, arena)?;
        let collapsed = collapse(l, self.op, r, arena);
        let res = match collapsed {
            MaybeCollapsed::Concretes(l, op, r) => {
                RangeExpr::new(l, op, r).exec_op(true, analyzer, arena)
            }
            MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
            MaybeCollapsed::Not(l, op, r) => {
                let res = RangeExpr::new(l, op, r).simplify_exec_op(true, analyzer, arena)?;
                match res {
                    Elem::Expr(expr) => match collapse(*expr.lhs, expr.op, *expr.rhs, arena) {
                        MaybeCollapsed::Concretes(l, op, r) => {
                            RangeExpr::new(l, op, r).exec_op(true, analyzer, arena)
                        }
                        MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
                        MaybeCollapsed::Not(l, op, r) => Ok(Elem::Expr(RangeExpr::new(l, op, r))),
                    },
                    other => Ok(other),
                }
            }
        }?;
        self.set_arenaized_flattened(true, res.clone(), arena);
        Ok(res)
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_min) = &self.flattened_min {
            return Ok(*simp_min.clone());
        }

        if let Some(arenaized) = self.arenaized_flat_cache(false, arena) {
            return Ok(*arenaized);
        }

        let l = self.lhs.simplify_minimize(analyzer, arena)?;
        self.lhs.set_arenaized_flattened(false, &l, arena);
        let r = self.rhs.simplify_minimize(analyzer, arena)?;
        self.rhs.set_arenaized_flattened(false, &r, arena);

        let collapsed = collapse(l, self.op, r, arena);
        let res = match collapsed {
            MaybeCollapsed::Concretes(l, op, r) => {
                RangeExpr::new(l, op, r).exec_op(false, analyzer, arena)
            }
            MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
            MaybeCollapsed::Not(l, op, r) => {
                let res = RangeExpr::new(l, op, r).simplify_exec_op(false, analyzer, arena)?;
                match res {
                    Elem::Expr(expr) => match collapse(*expr.lhs, expr.op, *expr.rhs, arena) {
                        MaybeCollapsed::Concretes(l, op, r) => {
                            return RangeExpr::new(l, op, r).exec_op(false, analyzer, arena)
                        }
                        MaybeCollapsed::Collapsed(collapsed) => return Ok(collapsed),
                        MaybeCollapsed::Not(l, op, r) => Ok(Elem::Expr(RangeExpr::new(l, op, r))),
                    },
                    other => Ok(other),
                }
            }
        }?;

        self.set_arenaized_flattened(false, res.clone(), arena);
        Ok(res)
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn cache_flatten(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        self.arenaize(g, arena)?;

        fn simp_minimize(
            this: &mut Elem<Concrete>,
            analyzer: &mut impl GraphBackend,
            arena: &mut RangeArena<Elem<Concrete>>,
        ) -> Result<Elem<Concrete>, GraphError> {
            let Elem::Expr(this) = this else {
                this.cache_flatten(analyzer, arena)?;
                if let Some(t) = this.arenaized_flattened(false, arena) {
                    return Ok(*t);
                } else {
                    return Ok(this.clone());
                }
            };

            if let Some(simp_min) = &this.flattened_min {
                return Ok(*simp_min.clone());
            }

            if let Some(arenaized) = this.arenaized_flat_cache(false, arena) {
                return Ok(*arenaized);
            }

            let l = simp_minimize(&mut this.lhs, analyzer, arena)?;
            let r = simp_minimize(&mut this.rhs, analyzer, arena)?;
            let collapsed = collapse(l, this.op, r, arena);
            let res = match collapsed {
                MaybeCollapsed::Concretes(l, op, r) => {
                    RangeExpr::new(l, op, r).exec_op(false, analyzer, arena)
                }
                MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
                MaybeCollapsed::Not(l, op, r) => {
                    let res = RangeExpr::new(l, op, r).simplify_exec_op(false, analyzer, arena)?;

                    let idx = arena.idx_or_upsert(res.clone(), analyzer);
                    match res {
                        Elem::Expr(expr) => match collapse(*expr.lhs, expr.op, *expr.rhs, arena) {
                            MaybeCollapsed::Concretes(l, op, r) => {
                                let exec_res =
                                    RangeExpr::new(l, op, r).exec_op(false, analyzer, arena)?;
                                Elem::Arena(idx).set_arenaized_flattened(false, &exec_res, arena);
                                Ok(exec_res)
                            }
                            MaybeCollapsed::Collapsed(collapsed) => {
                                Elem::Arena(idx).set_arenaized_flattened(false, &collapsed, arena);
                                Ok(collapsed)
                            }
                            MaybeCollapsed::Not(l, op, r) => {
                                Ok(Elem::Expr(RangeExpr::new(l, op, r)))
                            }
                        },
                        other => Ok(other),
                    }
                }
            }?;

            this.set_arenaized_flattened(false, res.clone(), arena);
            Ok(res)
        }

        fn simp_maximize(
            this: &mut Elem<Concrete>,
            analyzer: &mut impl GraphBackend,
            arena: &mut RangeArena<Elem<Concrete>>,
        ) -> Result<Elem<Concrete>, GraphError> {
            let Elem::Expr(this) = this else {
                this.cache_flatten(analyzer, arena)?;
                if let Some(t) = this.arenaized_flattened(true, arena) {
                    return Ok(*t);
                } else {
                    return Ok(this.clone());
                }
            };

            if let Some(simp_min) = &this.flattened_max {
                return Ok(*simp_min.clone());
            }

            if let Some(arenaized) = this.arenaized_flat_cache(false, arena) {
                return Ok(*arenaized);
            }

            let l = simp_maximize(&mut this.lhs, analyzer, arena)?;
            let r = simp_maximize(&mut this.rhs, analyzer, arena)?;
            let collapsed = collapse(l, this.op, r, arena);
            let res = match collapsed {
                MaybeCollapsed::Concretes(l, op, r) => {
                    RangeExpr::new(l, op, r).exec_op(true, analyzer, arena)
                }
                MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
                MaybeCollapsed::Not(l, op, r) => {
                    let res = RangeExpr::new(l, op, r).simplify_exec_op(true, analyzer, arena)?;

                    let idx = arena.idx_or_upsert(res.clone(), analyzer);
                    match res {
                        Elem::Expr(expr) => match collapse(*expr.lhs, expr.op, *expr.rhs, arena) {
                            MaybeCollapsed::Concretes(l, op, r) => {
                                let exec_res =
                                    RangeExpr::new(l, op, r).exec_op(true, analyzer, arena)?;
                                Elem::Arena(idx).set_arenaized_flattened(true, &exec_res, arena);
                                Ok(exec_res)
                            }
                            MaybeCollapsed::Collapsed(collapsed) => {
                                Elem::Arena(idx).set_arenaized_flattened(true, &collapsed, arena);
                                Ok(collapsed)
                            }
                            MaybeCollapsed::Not(l, op, r) => {
                                Ok(Elem::Expr(RangeExpr::new(l, op, r)))
                            }
                        },
                        other => Ok(other),
                    }
                }
            }?;

            this.set_arenaized_flattened(false, res.clone(), arena);
            Ok(res)
        }

        if self.flattened_max.is_none() {
            if let Some(idx) = self.arena_idx(arena) {
                if let Some(Elem::Expr(ref arenaized)) = arena.ranges.get(idx) {
                    if arenaized.flattened_max.is_some() {
                        return Ok(());
                    }
                };
            } else {
                self.arenaize(g, arena)?;
            }

            self.lhs.cache_flatten(g, arena)?;
            self.rhs.cache_flatten(g, arena)?;

            let mut flat_max = self.flatten(true, g, arena)?;
            let simplified_flat_max = simp_maximize(&mut flat_max, g, arena)?;
            simplified_flat_max.clone().arenaize(g, arena)?;
            self.flattened_max = Some(Box::new(simplified_flat_max));
        }

        if self.flattened_min.is_none() {
            if let Some(idx) = self.arena_idx(arena) {
                if let Some(Elem::Expr(ref arenaized)) = arena.ranges.get(idx) {
                    if arenaized.flattened_min.is_some() {
                        return Ok(());
                    }
                };
            } else {
                self.arenaize(g, arena)?;
            }

            self.lhs.cache_flatten(g, arena)?;
            self.rhs.cache_flatten(g, arena)?;

            let mut flat_min = self.flatten(false, g, arena)?;
            let simplified_flat_min = simp_minimize(&mut flat_min, g, arena)?;
            simplified_flat_min.clone().arenaize(g, arena)?;
            self.flattened_min = Some(Box::new(simplified_flat_min));
        }
        Ok(())
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn cache_maximize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        tracing::trace!("cache maximizing: {}", Elem::Expr(self.clone()));
        self.arenaize(g, arena)?;
        if self.maximized.is_none() {
            self.lhs.cache_maximize(g, arena)?;
            self.rhs.cache_maximize(g, arena)?;
            self.cache_exec_op(true, g, arena)?;
        }
        Ok(())
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    fn cache_minimize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        tracing::trace!("cache minimizing: {}", Elem::Expr(self.clone()));
        self.arenaize(g, arena)?;
        if self.minimized.is_none() {
            tracing::trace!("cache minimize lhs");
            self.lhs.cache_minimize(g, arena)?;
            tracing::trace!("cache minimize rhs");
            self.rhs.cache_minimize(g, arena)?;
            tracing::trace!("minimizing expr");
            self.cache_exec_op(false, g, arena)?;
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.uncache_exec();
    }
}
