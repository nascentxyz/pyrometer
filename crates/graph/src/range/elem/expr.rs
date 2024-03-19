use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{
        elem::{Elem, MinMaxed, RangeElem, RangeOp},
        exec_traits::*,
    },
    GraphBackend, GraphError,
};
use std::hash::Hash;
use std::hash::Hasher;

use ethers_core::types::U256;
use shared::NodeIdx;

pub static SINGLETON_EQ_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
];

pub static EQ_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
    RangeOp::And,
    RangeOp::Or,
];

pub static FLIP_INEQ_OPS: &[RangeOp] = &[RangeOp::Lt, RangeOp::Lte, RangeOp::Gt, RangeOp::Gte];

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

impl<T: std::cmp::PartialEq> PartialEq for RangeExpr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.lhs == other.lhs && self.rhs == other.rhs && self.op == other.op
    }
}
impl<T: std::cmp::PartialEq> Eq for RangeExpr<T> {}

impl Hash for RangeExpr<Concrete> {
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

    pub fn recurse_dearenaize(&self, analyzer: &impl GraphBackend) -> Elem<Concrete> {
        Elem::Expr(Self::new(
            self.lhs.recurse_dearenaize(analyzer).clone(),
            self.op,
            self.rhs.recurse_dearenaize(analyzer).clone(),
        ))
    }

    pub fn arena_idx(&self, analyzer: &impl GraphBackend) -> Option<usize> {
        let expr = Elem::Expr(RangeExpr::new(
            Elem::Arena(analyzer.range_arena_idx(&self.lhs)?),
            self.op,
            Elem::Arena(analyzer.range_arena_idx(&self.rhs)?),
        ));
        analyzer.range_arena_idx(&expr)
    }

    pub fn arenaized_cache(
        &self,
        max: bool,
        analyzer: &impl GraphBackend,
    ) -> Option<MinMaxed<Concrete>> {
        if let Some(idx) = self.arena_idx(analyzer) {
            let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() else {
                return None;
            };
            let Elem::Expr(ref arenaized) = *t else {
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
        analyzer: &impl GraphBackend,
    ) -> Option<Box<Elem<Concrete>>> {
        if let Some(idx) = self.arena_idx(analyzer) {
            let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() else {
                return None;
            };
            let Elem::Expr(ref arenaized) = *t else {
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
        analyzer: &impl GraphBackend,
    ) {
        if let Some(idx) = self.arena_idx(analyzer) {
            if let Ok(mut t) = analyzer.range_arena().ranges[idx].try_borrow_mut() {
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

    #[tracing::instrument(level = "trace", skip_all)]
    fn arenaize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        // self.lhs.clone().arenaize(analyzer)?;
        // self.rhs.clone().arenaize(analyzer)?;
        if self.arena_idx(analyzer).is_none() {
            let lhs = std::mem::take(&mut self.lhs);
            let rhs = std::mem::take(&mut self.rhs);
            self.lhs = Box::new(Elem::Arena(analyzer.range_arena_idx_or_upsert(*lhs)));
            self.rhs = Box::new(Elem::Arena(analyzer.range_arena_idx_or_upsert(*rhs)));
            let _ = analyzer.range_arena_idx_or_upsert(Elem::Expr(self.clone()));
        }
        Ok(())
    }

    fn range_eq(&self, _other: &Self, _analyzer: &impl GraphBackend) -> bool {
        false
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        match (maximize, &self.flattened_min, &self.flattened_max) {
            (true, _, Some(flat)) | (false, Some(flat), _) => {
                return Ok(*flat.clone());
            }
            _ => {}
        }

        if let Some(arenaized) = self.arenaized_flat_cache(maximize, analyzer) {
            return Ok(*arenaized);
        }

        Ok(Elem::Expr(RangeExpr::new(
            self.lhs.flatten(maximize, analyzer)?,
            self.op,
            self.rhs.flatten(maximize, analyzer)?,
        )))
    }

    fn is_flatten_cached(&self, analyzer: &impl GraphBackend) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some() || {
            if let Some(idx) = self.arena_idx(analyzer) {
                if let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() {
                    if let Elem::Expr(ref arenaized) = *t {
                        arenaized.flattened_min.is_some() && arenaized.flattened_max.is_some()
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        }
    }

    fn is_min_max_cached(&self, analyzer: &impl GraphBackend) -> (bool, bool) {
        let (arena_cached_min, arena_cached_max) = {
            if let Some(idx) = self.arena_idx(analyzer) {
                if let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() {
                    if let Elem::Expr(ref arenaized) = *t {
                        (arenaized.minimized.is_some(), arenaized.maximized.is_some())
                    } else {
                        (false, false)
                    }
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
        _analyzer: &impl GraphBackend,
    ) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on(analyzer);
        deps.extend(self.rhs.dependent_on(analyzer));
        deps
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps = self.lhs.recursive_dependent_on(analyzer)?;
        deps.extend(self.rhs.recursive_dependent_on(analyzer)?);
        Ok(deps)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let lhs_has_cycle = self.lhs.has_cycle(seen, analyzer)?;
        let rhs_has_cycle = self.rhs.has_cycle(seen, analyzer)?;
        Ok(lhs_has_cycle || rhs_has_cycle)
    }

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, Self::GraphError> {
        let lhs_deps_on = self.lhs.depends_on(var, seen, analyzer)?;
        let rhs_deps_on = self.rhs.depends_on(var, seen, analyzer)?;
        Ok(lhs_deps_on || rhs_deps_on)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
    ) {
        let _ = self.arenaize(analyzer);
        self.lhs.filter_recursion(node_idx, new_idx, analyzer);
        self.rhs.filter_recursion(node_idx, new_idx, analyzer);
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            Ok(*cached)
        } else if let Some(MinMaxed::Maximized(cached)) = self.arenaized_cache(true, analyzer) {
            Ok(*cached)
        } else if self.op == RangeOp::SetIndices {
            self.simplify_exec_op(true, analyzer)
        } else {
            self.exec_op(true, analyzer)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            Ok(*cached)
        } else if let Some(MinMaxed::Minimized(cached)) = self.arenaized_cache(false, analyzer) {
            Ok(*cached)
        } else if self.op == RangeOp::SetIndices {
            self.simplify_exec_op(false, analyzer)
        } else {
            self.exec_op(false, analyzer)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_max) = &self.flattened_max {
            return Ok(*simp_max.clone());
        }

        if let Some(arenaized) = self.arenaized_flat_cache(true, analyzer) {
            return Ok(*arenaized);
        }

        let l = self.lhs.simplify_maximize(analyzer)?;
        let r = self.rhs.simplify_maximize(analyzer)?;
        let collapsed = collapse(&l, self.op, &r, analyzer);
        let res = match collapsed {
            MaybeCollapsed::Concretes(..) => RangeExpr::new(l, self.op, r).exec_op(true, analyzer),
            MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
            MaybeCollapsed::Not(..) => {
                // Ok(Elem::Expr(RangeExpr::new(l, self.op, r)))//.simplify_exec_op(false, &mut vec![], analyzer)
                let res = RangeExpr::new(l, self.op, r).simplify_exec_op(true, analyzer)?;
                match res {
                    Elem::Expr(expr) => {
                        match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                            MaybeCollapsed::Concretes(..) => return expr.exec_op(true, analyzer),
                            MaybeCollapsed::Collapsed(collapsed) => return Ok(collapsed),
                            _ => {}
                        }
                        Ok(Elem::Expr(expr))
                    }
                    other => Ok(other),
                }
            }
        }?;
        self.set_arenaized_flattened(true, res.clone(), analyzer);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_min) = &self.flattened_min {
            return Ok(*simp_min.clone());
        }

        if let Some(arenaized) = self.arenaized_flat_cache(false, analyzer) {
            return Ok(*arenaized);
        }

        let l = self.lhs.simplify_minimize(analyzer)?;
        self.lhs.set_arenaized_flattened(false, &l, analyzer);
        let r = self.rhs.simplify_minimize(analyzer)?;
        self.rhs.set_arenaized_flattened(false, &r, analyzer);

        let collapsed = collapse(&l, self.op, &r, analyzer);
        let res = match collapsed {
            MaybeCollapsed::Concretes(..) => RangeExpr::new(l, self.op, r).exec_op(false, analyzer),
            MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
            MaybeCollapsed::Not(..) => {
                let res = RangeExpr::new(l, self.op, r).simplify_exec_op(false, analyzer)?;
                match res {
                    Elem::Expr(expr) => {
                        match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                            MaybeCollapsed::Concretes(..) => return expr.exec_op(false, analyzer),
                            MaybeCollapsed::Collapsed(collapsed) => return Ok(collapsed),
                            _ => {}
                        }
                        Ok(Elem::Expr(expr))
                    }
                    other => Ok(other),
                }
            }
        }?;

        self.set_arenaized_flattened(false, res.clone(), analyzer);
        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cache_flatten(&mut self, g: &mut impl GraphBackend) -> Result<(), GraphError> {
        self.arenaize(g)?;

        fn simplify_minimize(
            mut this: Elem<Concrete>,
            analyzer: &mut impl GraphBackend,
        ) -> Result<Elem<Concrete>, GraphError> {
            let Elem::Expr(this) = this else {
                this.cache_flatten(analyzer)?;
                if let Some(t) = this.arenaized_flattened(false, analyzer) {
                    return Ok(*t);
                } else {
                    return Ok(this.clone());
                }
            };

            if let Some(simp_min) = &this.flattened_min {
                return Ok(*simp_min.clone());
            }

            if let Some(arenaized) = this.arenaized_flat_cache(false, analyzer) {
                return Ok(*arenaized);
            }

            let l = this.lhs.simplify_minimize(analyzer)?;
            let r = this.rhs.simplify_minimize(analyzer)?;
            let collapsed = collapse(&l, this.op, &r, analyzer);
            let res = match collapsed {
                MaybeCollapsed::Concretes(..) => {
                    RangeExpr::new(l, this.op, r).exec_op(false, analyzer)
                }
                MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
                MaybeCollapsed::Not(..) => {
                    let res = RangeExpr::new(l, this.op, r).simplify_exec_op(false, analyzer)?;

                    let idx = analyzer.range_arena_idx_or_upsert(res.clone());
                    match res {
                        Elem::Expr(expr) => {
                            match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                                MaybeCollapsed::Concretes(..) => {
                                    let exec_res = expr.exec_op(false, analyzer)?;
                                    Elem::Arena(idx)
                                        .set_arenaized_flattened(false, &exec_res, analyzer);
                                    return Ok(exec_res);
                                }
                                MaybeCollapsed::Collapsed(collapsed) => {
                                    Elem::Arena(idx)
                                        .set_arenaized_flattened(false, &collapsed, analyzer);
                                    return Ok(collapsed);
                                }
                                _ => {}
                            }
                            Ok(Elem::Expr(expr))
                        }
                        other => Ok(other),
                    }
                }
            }?;

            this.set_arenaized_flattened(false, res.clone(), analyzer);
            Ok(res)
        }

        fn simplify_maximize(
            mut this: Elem<Concrete>,
            analyzer: &mut impl GraphBackend,
        ) -> Result<Elem<Concrete>, GraphError> {
            let Elem::Expr(this) = this else {
                this.cache_flatten(analyzer)?;
                if let Some(t) = this.arenaized_flattened(true, analyzer) {
                    return Ok(*t);
                } else {
                    return Ok(this.clone());
                }
            };

            if let Some(simp_min) = &this.flattened_max {
                return Ok(*simp_min.clone());
            }

            if let Some(arenaized) = this.arenaized_flat_cache(false, analyzer) {
                return Ok(*arenaized);
            }

            let l = this.lhs.simplify_maximize(analyzer)?;
            let r = this.rhs.simplify_maximize(analyzer)?;
            let collapsed = collapse(&l, this.op, &r, analyzer);
            let res = match collapsed {
                MaybeCollapsed::Concretes(..) => {
                    RangeExpr::new(l, this.op, r).exec_op(true, analyzer)
                }
                MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
                MaybeCollapsed::Not(..) => {
                    let res = RangeExpr::new(l, this.op, r).simplify_exec_op(true, analyzer)?;

                    let idx = analyzer.range_arena_idx_or_upsert(res.clone());
                    match res {
                        Elem::Expr(expr) => {
                            match collapse(&expr.lhs, expr.op, &expr.rhs, analyzer) {
                                MaybeCollapsed::Concretes(..) => {
                                    let exec_res = expr.exec_op(true, analyzer)?;
                                    Elem::Arena(idx)
                                        .set_arenaized_flattened(true, &exec_res, analyzer);
                                    return Ok(exec_res);
                                }
                                MaybeCollapsed::Collapsed(collapsed) => {
                                    Elem::Arena(idx)
                                        .set_arenaized_flattened(true, &collapsed, analyzer);
                                    return Ok(collapsed);
                                }
                                _ => {}
                            }
                            Ok(Elem::Expr(expr))
                        }
                        other => Ok(other),
                    }
                }
            }?;

            this.set_arenaized_flattened(false, res.clone(), analyzer);
            Ok(res)
        }

        if self.flattened_max.is_none() {
            if let Some(idx) = self.arena_idx(g) {
                if let Elem::Expr(ref arenaized) = *g.range_arena().ranges[idx].borrow() {
                    if arenaized.flattened_max.is_some() {
                        return Ok(());
                    }
                };
            } else {
                self.arenaize(g)?;
            }

            self.lhs.cache_flatten(g)?;
            self.rhs.cache_flatten(g)?;
            // self.arenaize(g)?;
            let flat_max = self.flatten(true, g)?;
            let simplified_flat_max = simplify_maximize(flat_max, g)?;
            simplified_flat_max.clone().arenaize(g)?;
            self.flattened_max = Some(Box::new(simplified_flat_max));
        }

        if self.flattened_min.is_none() {
            if let Some(idx) = self.arena_idx(g) {
                if let Elem::Expr(ref arenaized) = *g.range_arena().ranges[idx].borrow() {
                    if arenaized.flattened_min.is_some() {
                        return Ok(());
                    }
                };
            } else {
                self.arenaize(g)?;
            }

            self.lhs.cache_flatten(g)?;
            self.rhs.cache_flatten(g)?;
            // self.arenaize(g)?;
            let flat_min = self.flatten(false, g)?;
            let simplified_flat_min = simplify_minimize(flat_min, g)?;
            simplified_flat_min.clone().arenaize(g)?;
            self.flattened_min = Some(Box::new(simplified_flat_min));
        }
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cache_maximize(&mut self, g: &mut impl GraphBackend) -> Result<(), GraphError> {
        tracing::trace!("cache maximizing: {}", Elem::Expr(self.clone()));
        self.arenaize(g)?;
        if self.maximized.is_none() {
            self.lhs.cache_maximize(g)?;
            self.rhs.cache_maximize(g)?;
            self.cache_exec_op(true, g)?;
        }
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cache_minimize(&mut self, g: &mut impl GraphBackend) -> Result<(), GraphError> {
        tracing::trace!("cache minimizing: {}", Elem::Expr(self.clone()));
        self.arenaize(g)?;
        if self.minimized.is_none() {
            self.lhs.cache_minimize(g)?;
            self.rhs.cache_minimize(g)?;
            self.cache_exec_op(false, g)?;
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.uncache_exec();
    }
}

pub enum MaybeCollapsed<'a, 'b> {
    Concretes(&'a Elem<Concrete>, &'b Elem<Concrete>),
    Collapsed(Elem<Concrete>),
    Not(&'a Elem<Concrete>, &'b Elem<Concrete>),
}

pub fn collapse<'a, 'b, 'c: 'a + 'b>(
    l: &'a Elem<Concrete>,
    op: RangeOp,
    r: &'b Elem<Concrete>,
    analyzer: &'c impl GraphBackend,
) -> MaybeCollapsed<'a, 'b> {
    let zero = Elem::from(Concrete::from(U256::zero()));
    let one = Elem::from(Concrete::from(U256::one()));
    match (l, r) {
        (Elem::Arena(_), r) => {
            if let Ok(t) = l.dearenaize(analyzer).try_borrow() {
                match collapse(&t, op, r, analyzer) {
                    MaybeCollapsed::Not(..) => MaybeCollapsed::Not(l, r),
                    MaybeCollapsed::Concretes(..) => MaybeCollapsed::Concretes(l, r),
                    MaybeCollapsed::Collapsed(e) => MaybeCollapsed::Collapsed(e),
                }
            } else {
                MaybeCollapsed::Not(l, r)
            }
        }
        (l, Elem::Arena(_)) => {
            if let Ok(t) = r.dearenaize(analyzer).try_borrow() {
                match collapse(l, op, &t, analyzer) {
                    MaybeCollapsed::Not(..) => MaybeCollapsed::Not(l, r),
                    MaybeCollapsed::Concretes(..) => MaybeCollapsed::Concretes(l, r),
                    MaybeCollapsed::Collapsed(e) => MaybeCollapsed::Collapsed(e),
                }
            } else {
                MaybeCollapsed::Not(l, r)
            }
        }
        (Elem::Concrete(_), Elem::Concrete(_)) => MaybeCollapsed::Concretes(l, r),
        (Elem::Expr(expr), d @ Elem::Reference(_)) => {
            // try to collapse the expression
            let x = &*expr.lhs;
            let y = &*expr.rhs;
            let z = d;

            let x_ord_z = x.range_ord(z, analyzer);
            let x_eq_z = matches!(x_ord_z, Some(std::cmp::Ordering::Equal));

            let y_ord_z = y.range_ord(z, analyzer);
            let y_eq_z = matches!(y_ord_z, Some(std::cmp::Ordering::Equal));

            let y_eq_zero = matches!(
                y.range_ord(&zero, analyzer),
                Some(std::cmp::Ordering::Equal) | None
            );
            let x_eq_zero = matches!(
                x.range_ord(&zero, analyzer),
                Some(std::cmp::Ordering::Equal) | None
            );
            let y_eq_one = matches!(
                y.range_ord(&one, analyzer),
                Some(std::cmp::Ordering::Equal) | None
            );
            let x_eq_one = matches!(
                x.range_ord(&one, analyzer),
                Some(std::cmp::Ordering::Equal) | None
            );
            match (expr.op, op) {
                (RangeOp::Sub(_), RangeOp::Eq) | (RangeOp::Div(_), RangeOp::Eq) => {
                    if x_eq_z && !y_eq_zero {
                        // (x -|/ k) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(_), RangeOp::Eq) => {
                    if (x_eq_z && !y_eq_zero) || (y_eq_z && !x_eq_zero) {
                        // (x +|* k) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Mul(_), RangeOp::Eq) => {
                    if (x_eq_z && !y_eq_one) || (y_eq_z && !x_eq_one) {
                        // (x +|* k) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                _ => MaybeCollapsed::Not(l, r),
            }
        }
        // if we have an expression, it fundamentally must have a dynamic in it
        (Elem::Expr(expr), c @ Elem::Concrete(_)) => {
            // potentially collapsible
            let x = &*expr.lhs;
            let y = &*expr.rhs;
            let z = c;

            match (expr.op, op) {
                (RangeOp::Sub(false), RangeOp::Min) => {
                    // min{x - y, z}
                    // if x <= z, then x - y will be the minimum if y >= 0
                    if matches!(
                        x.range_ord(z, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Less)
                    ) && matches!(
                        y.range_ord(&zero, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
                    ) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(false), RangeOp::Max) => {
                    // max{x + y, z}
                    // if x >= z, then x + y will be the maximum if y >= 0
                    // or if y >= z, then x + y will be the maximum if x >= 0
                    if (matches!(
                        x.range_ord(z, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
                    ) && matches!(
                        y.range_ord(&zero, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
                    )) || (matches!(
                        y.range_ord(z, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
                    ) && matches!(
                        x.range_ord(&zero, analyzer),
                        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
                    )) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Eq, RangeOp::Eq) => {
                    // ((x == y) == z)
                    // can skip if x and z eq
                    if let Some(std::cmp::Ordering::Equal) = x.range_ord(z, analyzer) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else if let Some(std::cmp::Ordering::Equal) = y.range_ord(z, analyzer) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else if z.range_eq(&Elem::from(Concrete::from(true)), analyzer) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(l_op), RangeOp::Add(r_op)) => {
                    // ((x + y) + z)
                    let op_fn = if l_op && r_op {
                        // unchecked
                        RangeAdd::range_wrapping_add
                    } else {
                        // checked
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                    };
                    if let Some(new) = op_fn(x, z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(y.clone(), op, new)))
                    } else if let Some(new) = op_fn(y, z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(x.clone(), op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(l_op), RangeOp::Sub(r_op)) => {
                    // ((x + y) - z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(z, analyzer) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && y >= z ==> x + (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(y, z) {
                                    let new_expr =
                                        Elem::Expr(RangeExpr::new(x.clone(), expr.op, new));
                                    MaybeCollapsed::Collapsed(new_expr)
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                            Some(std::cmp::Ordering::Less) => {
                                // y and z are concrete && y < z ==> x - (z - y)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(z, y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        RangeOp::Sub(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                            None => {
                                // x and z are concrete, if x >= z, just do (x - z) + y
                                // else do (y - (z - x))
                                match x.range_ord(z, analyzer) {
                                    Some(std::cmp::Ordering::Equal)
                                    | Some(std::cmp::Ordering::Greater) => {
                                        let op_fn = if l_op {
                                            // unchecked
                                            RangeSub::range_wrapping_sub
                                        } else {
                                            // checked
                                            <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                        };
                                        if let Some(new) = op_fn(y, z) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                x.clone(),
                                                expr.op,
                                                new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(l, r)
                                        }
                                    }
                                    Some(std::cmp::Ordering::Less) => {
                                        // (y - (z - x)) because z > x, therefore its (-k + y) ==> (y - k) where k = (x - z)
                                        let op_fn = if l_op {
                                            // unchecked
                                            RangeSub::range_wrapping_sub
                                        } else {
                                            // checked
                                            <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                        };
                                        if let Some(new) = op_fn(z, x) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                y.clone(),
                                                RangeOp::Sub(l_op),
                                                new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(l, r)
                                        }
                                    }
                                    None => MaybeCollapsed::Not(l, r),
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Sub(l_op), RangeOp::Add(r_op)) => {
                    // ((x - y) + z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(z, analyzer) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && z <= y ==> x - (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(y, z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        expr.op,
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                            Some(std::cmp::Ordering::Less) => {
                                // y and z are concrete && y < z ==> x + (z - y)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(z, y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        RangeOp::Add(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                            None => {
                                // x and z are concrete, just add them ==> (x + z) - y
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeAdd::range_wrapping_add
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                                };
                                if let Some(new) = op_fn(x, z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        new,
                                        expr.op,
                                        y.clone(),
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Mul(l_op), RangeOp::Mul(r_op)) => {
                    // ((x * y) * z)
                    if l_op == r_op {
                        let op_fn = if l_op {
                            // unchecked
                            RangeMul::range_wrapping_mul
                        } else {
                            // checked
                            <Elem<Concrete> as RangeMul<Concrete>>::range_mul
                        };
                        if let Some(new) = op_fn(x, z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                y.clone(),
                                op,
                                new,
                            )))
                        } else if let Some(new) = op_fn(y, z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                x.clone(),
                                op,
                                new,
                            )))
                        } else {
                            MaybeCollapsed::Not(l, r)
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(wrapping), op) if EQ_OPS.contains(&op) => {
                    let const_op = if wrapping {
                        RangeSub::range_wrapping_sub
                    } else {
                        RangeSub::range_sub
                    };
                    // ((x + y) == z) => (x == (z - y)) || (y == (z - x))
                    // ..
                    // ((x + y) != z) => (x != (z - y)) || (y != (z - x))
                    if let Some(new) = const_op(z, y) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(y.clone(), op, new)))
                    } else if let Some(new) = const_op(z, x) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(x.clone(), op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Sub(wrapping), op) if EQ_OPS.contains(&op) => {
                    let op_y = if wrapping {
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_wrapping_add
                    } else {
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                    };
                    let op_x = if wrapping {
                        <Elem<Concrete> as RangeSub<Concrete>>::range_wrapping_sub
                    } else {
                        <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                    };
                    // ((x - y) == z) => (x == (z + y)) || (y == (x - z))
                    // ((x - y) != z) => (x != (z + y)) || (y != (x - z))
                    if let Some(new) = op_x(x, z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(y.clone(), op, new)))
                    } else if let Some(new) = op_y(y, z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(x.clone(), op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Mul(wrapping), op) if EQ_OPS.contains(&op) => {
                    let div_op = if wrapping {
                        RangeDiv::range_wrapping_div
                    } else {
                        RangeDiv::range_div
                    };
                    // ((x * y) == z) => (x == (z / y)) || (y == (z / x))
                    // ((x * y) != z) => (x != (z / y)) || (y != (z / x))
                    if let Some(new) = div_op(z, x) {
                        let new_op = if matches!(
                            x.range_ord(&zero, analyzer),
                            Some(std::cmp::Ordering::Less)
                        ) && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            y.clone(),
                            new_op,
                            new,
                        )))
                    } else if let Some(new) = div_op(z, y) {
                        let new_op = if matches!(
                            y.range_ord(&zero, analyzer),
                            Some(std::cmp::Ordering::Less)
                        ) && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            new_op,
                            new,
                        )))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Div(wrapping), op) if EQ_OPS.contains(&op) => {
                    let mul_op = if wrapping {
                        <Elem<Concrete> as RangeMul<Concrete>>::range_wrapping_mul
                    } else {
                        <Elem<Concrete> as RangeMul<Concrete>>::range_mul
                    };
                    let div_op = if wrapping {
                        <Elem<Concrete> as RangeDiv<Concrete>>::range_wrapping_div
                    } else {
                        <Elem<Concrete> as RangeDiv<Concrete>>::range_div
                    };

                    // ((x / y) == z) => (x == (z * y)) || (y == (x / z))
                    // ..
                    // ((x / y) != z) => (x != (z / y)) || (y != (x / z))
                    if let Some(new) = mul_op(z, y) {
                        let new_op = if matches!(
                            y.range_ord(&zero, analyzer),
                            Some(std::cmp::Ordering::Less)
                        ) && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            new_op,
                            new,
                        )))
                    } else if !FLIP_INEQ_OPS.contains(&op) {
                        if let Some(new) = div_op(x, z) {
                            // y is the dynamic element
                            // we cant do flip ops here because we do (x / y) * y >= z * y which is a flip potentially
                            // but we dont know if y was negative. so we limit to just eq & neq
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                y.clone(),
                                op,
                                new,
                            )))
                        } else {
                            MaybeCollapsed::Not(l, r)
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (_, RangeOp::Eq) => {
                    // (x _ y) == z ==> (x _ y if z == true)
                    if z.range_eq(&Elem::from(Concrete::from(true)), analyzer) {
                        MaybeCollapsed::Collapsed(l.clone())
                    } else if z.range_eq(&Elem::from(Concrete::from(false)), analyzer) {
                        // (!x && !y)
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(l, r),
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (_, RangeOp::Neq) => {
                    // (x _ y) != z ==> (x _ y if z != false)
                    if z.range_eq(&Elem::from(Concrete::from(false)), analyzer) {
                        // != false is == true
                        MaybeCollapsed::Collapsed(l.clone())
                    } else if z.range_eq(&Elem::from(Concrete::from(true)), analyzer) {
                        // != true is == false, to make it == true, inverse everything
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(l, r),
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                _ => MaybeCollapsed::Not(l, r),
            }
        }
        (Elem::Concrete(_c), Elem::Expr(_expr)) => match collapse(r, op, l, analyzer) {
            MaybeCollapsed::Collapsed(inner) => MaybeCollapsed::Collapsed(inner.clone()),
            MaybeCollapsed::Not(_, _) => MaybeCollapsed::Not(l, r),
            MaybeCollapsed::Concretes(_, _) => unreachable!(),
        },
        (le @ Elem::Reference(_), c @ Elem::Concrete(_)) => match op {
            RangeOp::Sub(_) | RangeOp::Add(_) => {
                if matches!(
                    c.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Equal)
                ) {
                    MaybeCollapsed::Collapsed(le.clone())
                } else {
                    MaybeCollapsed::Not(l, r)
                }
            }
            RangeOp::Mul(_) | RangeOp::Div(_) => {
                if matches!(c.range_ord(&one, analyzer), Some(std::cmp::Ordering::Equal)) {
                    MaybeCollapsed::Collapsed(le.clone())
                } else {
                    MaybeCollapsed::Not(l, r)
                }
            }
            _ => MaybeCollapsed::Not(l, r),
        },
        _ => MaybeCollapsed::Not(l, r),
    }
}
