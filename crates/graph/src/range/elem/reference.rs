use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{
        elem::{Elem, MinMaxed, RangeConcrete, RangeElem, RangeOp},
        Range,
    },
    GraphBackend, GraphError, TypeNode, VarType,
};

use shared::NodeIdx;

use solang_parser::pt::Loc;

use std::collections::BTreeMap;

/// A dynamic range element value
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
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

    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.idx == other.idx {
            Some(std::cmp::Ordering::Equal)
        } else {
            None
        }
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        vec![self.idx.into()]
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps = ContextVarNode(self.idx.index()).dependent_on(analyzer, true)?;
        deps.push(ContextVarNode(self.idx.index()));
        Ok(deps)
    }

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let cvar = ContextVarNode::from(self.idx);
        let mut has_cycle = false;
        if seen.contains(&cvar) {
            Ok(true)
        } else {
            seen.push(cvar);
            if let Some(range) = cvar.ref_range(analyzer)? {
                has_cycle = has_cycle || range.min.has_cycle(seen, analyzer)?;
                has_cycle = has_cycle || range.max.has_cycle(seen, analyzer)?;
                Ok(has_cycle)
            } else {
                Ok(false)
            }
        }
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        if let Some(new) = mapping.get(&ContextVarNode::from(self.idx)) {
            self.idx = new.0.into();
        }
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        match (maximize, &self.flattened_min, &self.flattened_max) {
            (true, _, Some(flat)) | (false, Some(flat), _) => {
                // println!("flatten cache hit: {}", self.idx.index());
                return Ok(*flat.clone());
            }
            _ => {}
        }

        // println!("flatten cache miss: {}", self.idx.index());
        let cvar = ContextVarNode::from(self.idx);
        // println!("flattening reference: {} (idx_{})", cvar.display_name(analyzer)?, self.idx.index());
        if cvar.is_fundamental(analyzer)? {
            return Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )));
        }
        if maximize {
            cvar.range_max(analyzer)?
                .unwrap_or(Elem::Null)
                .flatten(maximize, analyzer)
        } else {
            let flattened = cvar
                .range_min(analyzer)?
                .unwrap_or(Elem::Null)
                .flatten(maximize, analyzer)?;
            Ok(flattened)
        }
    }

    fn is_flatten_cached(&self) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some()
    }

    fn cache_flatten(&mut self, g: &impl GraphBackend) -> Result<(), GraphError> {
        if self.flattened_max.is_none() {
            let flat_max = self.flatten(true, g)?;
            let simplified_flat_max = flat_max.simplify_maximize(&mut vec![], g)?;
            self.flattened_max = Some(Box::new(simplified_flat_max));
        }
        if self.flattened_min.is_none() {
            let flat_min = self.flatten(false, g)?;
            let simplified_flat_min = flat_min.simplify_minimize(&mut vec![], g)?;
            self.flattened_min = Some(Box::new(simplified_flat_min));
        }
        Ok(())
    }

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx) {}

    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_max(analyzer)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_min(analyzer)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_max) = &self.flattened_max {
            return Ok(*simp_max.clone());
        }

        let cvar = ContextVarNode::from(self.idx);

        let independent = cvar.is_fundamental(analyzer)?;
        if independent {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(true, analyzer)?
                .simplify_maximize(exclude, analyzer)
        }
    }

    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(simp_min) = &self.flattened_min {
            return Ok(*simp_min.clone());
        }

        let cvar = ContextVarNode::from(self.idx);
        if cvar.is_fundamental(analyzer)? {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(false, analyzer)?
                .simplify_minimize(exclude, analyzer)
        }
    }

    fn cache_maximize(&mut self, g: &impl GraphBackend) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.maximized = Some(MinMaxed::Maximized(Box::new(self.maximize(g)?)));
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphBackend) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.minimized = Some(MinMaxed::Minimized(Box::new(self.minimize(g)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
        self.flattened_min = None;
        self.flattened_max = None;
    }

    fn contains_op_set(
        &self,
        max: bool,
        op_set: &[RangeOp],
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    if max {
                        range.max.contains_op_set(max, op_set, analyzer)
                    } else {
                        range.min.contains_op_set(max, op_set, analyzer)
                    }
                } else {
                    Ok(false)
                }
            }
            VarType::Concrete(_concrete_node) => Ok(false),
            _e => Ok(false),
        }
    }
}
