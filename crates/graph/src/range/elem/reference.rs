use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{
        elem::{Elem, MinMaxed, RangeArenaLike, RangeConcrete, RangeElem},
        Range,
    },
    GraphBackend, TypeNode, VarType,
};
use std::hash::Hash;
use std::hash::Hasher;

use shared::{GraphError, NodeIdx, RangeArena};

use solang_parser::pt::Loc;

/// A dynamic range element value
#[derive(Clone, Debug, Ord, PartialOrd)]
pub struct Reference<T> {
    /// Index of the node that is referenced
    pub idx: NodeIdx,
    /// Cached minimized value
    pub minimized: Option<MinMaxed<T>>,
    /// Cached maximized value
    pub maximized: Option<MinMaxed<T>>,
    /// Cached minimized flatten value
    pub flattened_min: Option<Box<Elem<T>>>,
    /// Cached maximized flatten value
    pub flattened_max: Option<Box<Elem<T>>>,
}

impl<T> Hash for Reference<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.idx.hash(state);
    }
}

impl<T> PartialEq for Reference<T> {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
    }
}
impl<T> Eq for Reference<T> {}

impl<T> Reference<T> {
    pub fn new(idx: NodeIdx) -> Self {
        Self {
            idx,
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
        }
    }
}

impl RangeElem<Concrete> for Reference<Concrete> {
    type GraphError = GraphError;

    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        // let smol = Elem::Reference(Reference::new(self.idx));
        // if analyzer.range_arena_idx(&smol).is_none() {
        let _ = arena.idx_or_upsert(Elem::Reference(self.clone()), analyzer);
        // }
        Ok(())
    }

    fn range_eq(&self, _other: &Self, _arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        false
    }

    fn range_ord(
        &self,
        other: &Self,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<std::cmp::Ordering> {
        if self.idx == other.idx {
            Some(std::cmp::Ordering::Equal)
        } else {
            None
        }
    }

    fn dependent_on(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        vec![self.idx.into()]
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps = ContextVarNode(self.idx.index()).dependent_on(analyzer, true)?;
        deps.push(ContextVarNode(self.idx.index()));
        Ok(deps)
    }

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let cvar = ContextVarNode::from(self.idx);
        let mut has_cycle = false;
        if seen.contains(&cvar) {
            Ok(true)
        } else {
            seen.push(cvar);
            if let Some(range) = cvar.ref_range(analyzer)? {
                has_cycle = has_cycle || range.min.has_cycle(seen, analyzer, arena)?;
                has_cycle = has_cycle || range.max.has_cycle(seen, analyzer, arena)?;
                Ok(has_cycle)
            } else {
                Ok(false)
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
        let cvar = ContextVarNode::from(self.idx);
        if seen.contains(&cvar) {
            return Ok(false);
        }

        if cvar == var || cvar.name(analyzer)? == var.name(analyzer)? && self.idx >= var.0.into() {
            Ok(true)
        } else if let Some(range) = cvar.ref_range(analyzer)? {
            seen.push(cvar);
            let mut deps_on = range.min.depends_on(var, seen, analyzer, arena)?;
            deps_on |= range.max.depends_on(var, seen, analyzer, arena)?;
            Ok(deps_on)
        } else {
            Ok(false)
        }
    }

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

        let cvar = ContextVarNode::from(self.idx);
        if cvar.is_fundamental(analyzer)? {
            return Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )));
        }
        if maximize {
            cvar.range_max(analyzer)?
                .unwrap_or(Elem::Null)
                .flatten(maximize, analyzer, arena)
        } else {
            let flattened = cvar
                .range_min(analyzer)?
                .unwrap_or(Elem::Null)
                .flatten(maximize, analyzer, arena)?;
            Ok(flattened)
        }
    }

    fn is_flatten_cached(
        &self,
        _analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some() || {
            if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
                if let Some(t) = arena.ranges.get(idx) {
                    if let Elem::Reference(ref arenaized) = *t {
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

    fn is_min_max_cached(
        &self,
        _analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (bool, bool) {
        let (arena_cached_min, arena_cached_max) = {
            if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
                if let Some(t) = arena.ranges.get(idx) {
                    if let Elem::Reference(ref arenaized) = *t {
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

    fn cache_flatten(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        self.arenaize(g, arena)?;

        if self.flattened_max.is_none() {
            if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
                if let Some(t) = arena.ranges.get(idx) {
                    if let Elem::Reference(ref arenaized) = *t {
                        if arenaized.flattened_max.is_some() {
                            tracing::trace!("reference cache flatten hit");
                            return Ok(());
                        }
                    }
                }
            }

            let cvar = ContextVarNode::from(self.idx);
            cvar.cache_flattened_range(g, arena)?;
            let flat_max = self.flatten(true, g, arena)?;
            let simplified_flat_max = flat_max.simplify_maximize(g, arena)?;
            self.flattened_max = Some(Box::new(simplified_flat_max));
        }
        if self.flattened_min.is_none() {
            if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
                if let Some(t) = arena.ranges.get(idx) {
                    if let Elem::Reference(ref arenaized) = *t {
                        if arenaized.flattened_min.is_some() {
                            tracing::trace!("reference cache flatten hit");
                            return Ok(());
                        }
                    }
                }
            }
            let cvar = ContextVarNode::from(self.idx);
            cvar.cache_flattened_range(g, arena)?;
            let flat_min = self.flatten(false, g, arena)?;
            let simplified_flat_min = flat_min.simplify_minimize(g, arena)?;
            self.flattened_min = Some(Box::new(simplified_flat_min));
        }
        Ok(())
    }

    fn filter_recursion(
        &mut self,
        _: NodeIdx,
        _: NodeIdx,
        _analyzer: &mut impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) {
    }

    fn maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
            if let Some(t) = arena.ranges.get(idx) {
                if let Elem::Reference(ref arenaized) = *t {
                    tracing::trace!("reference maximize cache hit");
                    if let Some(MinMaxed::Maximized(cached)) = arenaized.maximized.clone() {
                        return Ok(*cached);
                    }
                }
            }
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_max(analyzer, arena)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete::new(
                concrete_node.underlying(analyzer)?.clone(),
                cvar.loc.unwrap_or(Loc::Implicit),
            ))),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
            if let Some(t) = arena.ranges.get(idx) {
                if let Elem::Reference(ref arenaized) = *t {
                    if let Some(MinMaxed::Minimized(cached)) = arenaized.minimized.clone() {
                        tracing::trace!("reference minimize cache hit");
                        return Ok(*cached);
                    }
                }
            }
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_min(analyzer, arena)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete::new(
                concrete_node.underlying(analyzer)?.clone(),
                cvar.loc.unwrap_or(Loc::Implicit),
            ))),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_max) = &self.flattened_max {
            return Ok(*simp_max.clone());
        }

        if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
            if let Some(t) = arena.ranges.get(idx) {
                if let Elem::Reference(ref arenaized) = *t {
                    if arenaized.flattened_max.is_some() {
                        tracing::trace!("reference simplify maximize cache hit");
                        return Ok(*arenaized.flattened_max.clone().unwrap());
                    }
                }
            }
        }

        let cvar = ContextVarNode::from(self.idx);

        let independent = cvar.is_fundamental(analyzer)?;
        if independent {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(true, analyzer, arena)?
                .simplify_maximize(analyzer, arena)
        }
    }

    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        let cvar = ContextVarNode::from(self.idx);
        if let Some(simp_min) = &self.flattened_min {
            return Ok(*simp_min.clone());
        }

        if let Some(idx) = arena.idx(&Elem::Reference(Reference::new(self.idx))) {
            if let Some(t) = arena.ranges.get(idx) {
                if let Elem::Reference(ref arenaized) = *t {
                    if arenaized.flattened_min.is_some() {
                        tracing::trace!("reference simplify minimize cache hit");
                        return Ok(*arenaized.flattened_min.clone().unwrap());
                    }
                }
            }
        }

        if cvar.is_fundamental(analyzer)? {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(false, analyzer, arena)?
                .simplify_minimize(analyzer, arena)
        }
    }

    fn cache_maximize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        self.arenaize(g, arena)?;
        if self.maximized.is_none() {
            let cvar = ContextVarNode::from(self.idx);
            cvar.cache_eval_range(g, arena)?;
            let max = self.maximize(g, arena)?;
            Elem::Reference(Reference::new(self.idx)).set_arenaized_cache(true, &max, arena);
            self.maximized = Some(MinMaxed::Maximized(Box::new(max)));
        }
        Ok(())
    }

    fn cache_minimize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        self.arenaize(g, arena)?;
        if self.minimized.is_none() {
            let cvar = ContextVarNode::from(self.idx);
            cvar.cache_eval_range(g, arena)?;
            let min = self.minimize(g, arena)?;
            Elem::Reference(Reference::new(self.idx)).set_arenaized_cache(false, &min, arena);
            self.minimized = Some(MinMaxed::Minimized(Box::new(min)));
        }

        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
        self.flattened_min = None;
        self.flattened_max = None;
    }
}
