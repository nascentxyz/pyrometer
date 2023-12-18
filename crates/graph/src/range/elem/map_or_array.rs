use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{Elem, MinMaxed, RangeElem, RangeOp},
    GraphBackend, GraphError,
};

use shared::NodeIdx;

use solang_parser::pt::Loc;

use std::collections::BTreeMap;

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeDyn<T> {
    /// Cached minimized value
    pub minimized: Option<MinMaxed<T>>,
    /// Cached maximized value
    pub maximized: Option<MinMaxed<T>>,
    pub flattened_min: Option<Box<Elem<T>>>,
    pub flattened_max: Option<Box<Elem<T>>>,
    /// Length of the dynamic variable
    pub len: Box<Elem<T>>,
    /// Values of the dynamic variable
    pub val: BTreeMap<Elem<T>, (Elem<T>, usize)>,
    /// An operations log
    pub op_num: usize,
    /// For recursion, sets whether to filter nulls
    // pub filter_null: bool,
    /// Sourcecode location
    pub loc: Loc,
}

impl<T: Ord> RangeDyn<T> {
    pub fn new_w_op_nums(len: Elem<T>, val: BTreeMap<Elem<T>, (Elem<T>, usize)>, loc: Loc) -> Self {
        let op_num = val.iter().fold(0, |mut acc, (_k, (_v, i))| {
            if i > &acc {
                acc = *i;
                acc
            } else {
                acc
            }
        });
        Self {
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
            len: Box::new(len),
            val,
            op_num,
            loc,
        }
    }
    pub fn new(len: Elem<T>, val: BTreeMap<Elem<T>, Elem<T>>, loc: Loc) -> Self {
        let mut op_num = 0;
        let val = val.into_iter().map(|(k, v)| {
            let res = (k, (v, op_num));
            op_num += 1;
            res
        }).collect();
        Self {
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
            len: Box::new(len),
            val,
            op_num,
            loc,
        }
    }

    pub fn new_for_indices(vals: Vec<(Elem<T>, Elem<T>)>, loc: Loc) -> Self {
        let mut op_num = 0;
        let val = vals.into_iter().map(|(k, v)| {
            let res = (k, (v, op_num));
            op_num += 1;
            res
        }).collect();
        Self {
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
            len: Box::new(Elem::Null),
            val,
            op_num,
            loc,
        }
    }

    /// Set the length
    pub fn set_len(&mut self, new_len: Elem<T>) {
        self.len = Box::new(new_len);
    }

    /// Check if the node contains a reference to a node index
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.len.contains_node(node_idx)
        // || self.val.iter().any(|(k, v)| k.contains_node(node_idx) || v.contains_node(node_idx))
    }
}

impl RangeDyn<Concrete> {

}

impl RangeElem<Concrete> for RangeDyn<Concrete> {
    type GraphError = GraphError;

    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.len.range_ord(&other.len) {
            Some(std::cmp::Ordering::Equal) => {
                let mut eq = 0;
                let mut self_lt = 0;
                let mut self_gt = 0;
                self.val.iter().zip(other.val.iter()).for_each(|((self_key, self_val), (other_key, other_val))| {
                    if let Some(std::cmp::Ordering::Equal) = self_key.clone().range_ord(other_key) {
                        match self_val.0.clone().range_ord(&other_val.0) {
                            Some(std::cmp::Ordering::Equal) => eq += 1,
                            Some(std::cmp::Ordering::Less) => self_lt += 1,
                            Some(std::cmp::Ordering::Greater) => self_gt += 1,
                            _ => {}
                        }
                    }
                });

                if self_lt == self.val.len() {
                    Some(std::cmp::Ordering::Less)
                } else if eq == self.val.len() {
                    Some(std::cmp::Ordering::Equal)
                } else if self_gt == self.val.len() {
                    Some(std::cmp::Ordering::Greater)
                } else {
                    None
                }
            }
            other => other
        }
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps: Vec<ContextVarNode> = self.len.dependent_on();
        deps.extend(
            self.val
                .iter()
                .flat_map(|(_, val)| val.0.dependent_on())
                .collect::<Vec<_>>(),
        );
        deps
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps: Vec<ContextVarNode> = self.len.recursive_dependent_on(analyzer)?;
        deps.extend(
            self.val
                .values()
                .map(|val| val.0.recursive_dependent_on(analyzer))
                .collect::<Result<Vec<Vec<_>>, _>>()?
                .iter()
                .flatten()
                .collect::<Vec<_>>(),
        );
        deps.extend(
            self.val
                .keys()
                .map(|key| key.recursive_dependent_on(analyzer))
                .collect::<Result<Vec<Vec<_>>, _>>()?
                .iter()
                .flatten()
                .collect::<Vec<_>>(),
        );
        Ok(deps)
    }

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let mut has_cycle = false;
        has_cycle = has_cycle || self.len.has_cycle(seen, analyzer)?;
        self.val.iter().try_for_each(|(_, val)| {
            has_cycle = has_cycle || val.0.has_cycle(seen, analyzer)?;
            Ok(())
        })?;
        Ok(has_cycle)
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        match (maximize, &self.flattened_min, &self.flattened_max) {
            (true, _, Some(flat)) | (false, Some(flat), _) => return Ok(*flat.clone()),
            _ => {}
        }
        Ok(Elem::ConcreteDyn(Self {
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
            len: Box::new(self.len.flatten(maximize, analyzer)?),
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(
                        idx.flatten(maximize, analyzer)?,
                        (val.0.flatten(maximize, analyzer)?, val.1)
                    );
                }
                map
            },
            op_num: self.op_num,
            loc: self.loc,
        }))
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

    fn is_flatten_cached(&self) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some()
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        self.len.update_deps(mapping);
        self.val
            .iter_mut()
            .for_each(|(_, val)| val.0.update_deps(mapping));
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.len.filter_recursion(node_idx, new_idx);
        self.val = self
            .val
            .clone()
            .into_iter()
            .map(|(mut k, mut v)| {
                k.filter_recursion(node_idx, new_idx);
                v.0.filter_recursion(node_idx, new_idx);
                (k, v)
            })
            .collect();
    }

    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.maximize(analyzer)?,
            {
                let mut map: BTreeMap<_, (Elem<Concrete>, usize)> = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont maximize the key so that any subsequent
                    // `get_index` can find potential values
                    let maximized = val.0.maximize(analyzer)?;
                    map.insert(idx.simplify_maximize(&mut vec![], analyzer)?, (maximized, val.1));
                }

                // map.into_iter().filter(|(k, (v, op))| {
                //     *v != Elem::Null
                // }).collect()
                map
            },
            self.loc,
        )))
    }

    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.minimize(analyzer)?,
            {
                let mut map: BTreeMap<_, (Elem<Concrete>, usize)> = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let minimized = val.0.minimize(analyzer)?;
                    map.insert(idx.simplify_minimize(&mut vec![], analyzer)?, (minimized, val.1));
                }

                // map.into_iter().filter(|(k, (v, op))| {
                //     *v != Elem::Null
                // }).collect()
                map
            },
            self.loc,
        )))
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(max) = &self.flattened_max {
            return Ok(*max.clone());
        }
        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.simplify_maximize(exclude, analyzer)?,
            {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let simplified = val.0.simplify_maximize(exclude, analyzer)?;
                    map.insert(idx, (simplified, val.1));
                }
                map
            },
            self.loc,
        )))

    }
    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(min) = &self.flattened_min {
            return Ok(*min.clone());
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.simplify_minimize(exclude, analyzer)?,
            {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let simplified = val.0.simplify_minimize(exclude, analyzer)?;
                    map.insert(idx, (simplified, val.1));
                }
                map
            },
            self.loc,
        )))
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
        // self.flattened_min = None;
        // self.flattened_max = None;
    }

    fn contains_op_set(
        &self,
        _max: bool,
        _op_set: &[RangeOp],
        _: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        // TODO: reevaluate this
        Ok(false)
    }
}
