use crate::{GraphError, nodes::{ContextVarNode, Concrete}};

use range::elem::{RangeElem, RangeOp, RangeDyn, MinMaxed, Elem};
use shared::{NodeIdx, GraphLike};

use std::collections::BTreeMap;

impl RangeElem<Concrete> for RangeDyn<Concrete> {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        None
    }

    fn dependent_on(&self) -> Vec<NodeIdx> {
        let mut deps: Vec<ContextVarNode> = self.len.dependent_on();
        deps.extend(
            self.val
                .iter()
                .flat_map(|(_, val)| val.dependent_on())
                .collect::<Vec<_>>(),
        );
        deps
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::ConcreteDyn(Box::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.flatten(maximize, analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.flatten(maximize, analyzer)?);
                }
                map
            },
            loc: self.loc,
        })))
    }

    fn update_deps(&mut self, mapping: &BTreeMap<NodeIdx, NodeIdx>) {
        self.len.update_deps(mapping);
        self.val
            .iter_mut()
            .for_each(|(_, val)| val.update_deps(mapping));
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.len.filter_recursion(node_idx, new_idx);
        self.val = self
            .val
            .clone()
            .into_iter()
            .map(|(mut k, mut v)| {
                k.filter_recursion(node_idx, new_idx);
                v.filter_recursion(node_idx, new_idx);
                (k, v)
            })
            .collect();
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Box::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.maximize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.maximize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        })))
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Box::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.minimize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.minimize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        })))
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::ConcreteDyn(Box::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.simplify_maximize(exclude, analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.simplify_maximize(exclude, analyzer)?);
                }
                map
            },
            loc: self.loc,
        })))
    }
    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::ConcreteDyn(Box::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.simplify_minimize(exclude, analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.simplify_minimize(exclude, analyzer)?);
                }
                map
            },
            loc: self.loc,
        })))
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.maximized = Some(MinMaxed::Maximized(Box::new(self.maximize(g)?)));
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.minimized = Some(MinMaxed::Minimized(Box::new(self.minimize(g)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
    }

    fn contains_op_set(
        &self,
        _max: bool,
        _op_set: &[RangeOp],
        _: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        // TODO: reevaluate this
        Ok(false)
    }
}