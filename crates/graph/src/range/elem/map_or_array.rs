use crate::{
    nodes::{Builtin, Concrete, ContextVarNode},
    range::{
        elem::{Elem, MinMaxed, RangeConcrete, RangeElem},
        exec_traits::{RangeCast, RangeMemLen},
    },
    GraphBackend, GraphError,
};

use shared::{NodeIdx, RangeArena};

use ethers_core::types::{H256, U256};
use solang_parser::pt::Loc;

use std::collections::BTreeMap;
use std::hash::Hash;
use std::hash::Hasher;

use super::rc_uint256;

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd)]
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

impl<T: std::cmp::PartialEq> PartialEq for RangeDyn<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.val == other.val && self.op_num == other.op_num
    }
}
impl<T: std::cmp::PartialEq> Eq for RangeDyn<T> {}

impl<T: Hash> Hash for RangeDyn<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self.len).hash(state);
        self.val.hash(state);
        self.op_num.hash(state);
    }
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
        let val = val
            .into_iter()
            .map(|(k, v)| {
                let res = (k, (v, op_num));
                op_num += 1;
                res
            })
            .collect();
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
        let val = vals
            .into_iter()
            .map(|(k, v)| {
                let res = (k, (v, op_num));
                op_num += 1;
                res
            })
            .collect();
        Self {
            minimized: None,
            maximized: None,
            flattened_min: None,
            flattened_max: None,
            len: Box::new(Elem::Null),
            val,
            op_num: op_num - 1,
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
    pub fn as_sized_bytes(&self) -> Option<Elem<Concrete>> {
        let len = self.range_get_length()?;
        let uint_val = len.maybe_concrete()?.val.uint_val()?;
        if uint_val <= 32.into() {
            let v = vec![0u8; uint_val.as_usize()];
            let conc = Concrete::from(v)
                .cast(Builtin::Bytes(uint_val.as_usize() as u8))
                .unwrap();
            let to_cast = RangeConcrete::new(conc, Loc::Implicit);
            self.range_cast(&to_cast)
        } else {
            None
        }
    }
    pub fn as_bytes(
        &self,
        analyzer: &impl GraphBackend,
        maximize: bool,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Vec<u8>> {
        let len = if maximize {
            let as_u256 = self
                .len
                .maximize(analyzer, arena)
                .ok()?
                .concrete()?
                .into_u256()?;
            if as_u256 > usize::MAX.into() {
                usize::MAX
            } else {
                as_u256.as_usize()
            }
        } else {
            let mut as_u256 = self
                .len
                .minimize(analyzer, arena)
                .ok()?
                .concrete()?
                .into_u256()?;
            if let Some(max_key) = self.evaled_max_key(analyzer, arena) {
                if let Some(max_key) = max_key.into_u256() {
                    as_u256 = as_u256.max(max_key);
                }
            }

            if as_u256 > usize::MAX.into() {
                usize::MAX
            } else {
                as_u256.as_usize()
            }
        };

        Some(
            self.val
                .values()
                .map(|v| v.0.as_bytes(analyzer, maximize, arena))
                .collect::<Option<Vec<Vec<u8>>>>()?
                .into_iter()
                .flatten()
                .take(len)
                .collect(),
        )
    }

    pub fn evaled_max_key(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Concrete> {
        let mut evaled = self
            .val
            .keys()
            .filter_map(|key| key.maximize(analyzer, arena).ok())
            .collect::<Vec<_>>();
        evaled.sort_by(|a, b| a.range_ord(b, arena).unwrap_or(std::cmp::Ordering::Less));

        evaled.iter().take(1).next()?.concrete()
    }

    pub fn from_concrete(concrete: Concrete, loc: Loc) -> Option<Self> {
        let (vals, len) = match concrete {
            Concrete::Bytes(size, b) => (
                Some(
                    b.0.into_iter()
                        .take((size).into())
                        .enumerate()
                        .map(|(i, b)| {
                            let mut h = H256::default();
                            h.0[0] = b;
                            (
                                rc_uint256(i as u128).into(),
                                RangeConcrete::new(Concrete::Bytes(1, h), Loc::Implicit).into(),
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
                Concrete::Uint(256, U256::from(size)),
            ),
            Concrete::DynBytes(b) => (
                Some(
                    b.iter()
                        .enumerate()
                        .map(|(i, by)| {
                            let mut h = H256::default();
                            h.0[0] = *by;
                            (
                                rc_uint256(i as u128).into(),
                                RangeConcrete::new(Concrete::Bytes(1, h), Loc::Implicit).into(),
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
                Concrete::Uint(256, U256::from(b.len())),
            ),
            Concrete::String(s) => (
                Some(
                    s.chars()
                        .enumerate()
                        .map(|(i, b): (usize, char)| {
                            let mut h = H256::default();
                            h.0[0] = b as u8;
                            (
                                rc_uint256(i as u128).into(),
                                RangeConcrete::new(Concrete::Bytes(1, h), Loc::Implicit).into(),
                            )
                        })
                        .collect::<Vec<_>>(),
                ),
                Concrete::Uint(256, U256::from(s.len())),
            ),
            _ => (None, Concrete::Uint(256, 0.into())),
        };

        let mut s = Self::new_for_indices(vals?, loc);
        s.len = Box::new(RangeConcrete::new(len, loc).into());
        Some(s)
    }
}

impl RangeElem<Concrete> for RangeDyn<Concrete> {
    type GraphError = GraphError;

    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        self.len.arenaize(analyzer, arena)?;
        self.val = self
            .val
            .iter_mut()
            .map(|(k, (v, op))| {
                let mut new_k = k.clone();
                let mut new_v = v.clone();
                new_k.arenaize(analyzer, arena);
                new_v.arenaize(analyzer, arena);
                (new_k, (new_v, *op))
            })
            .collect();
        Ok(())
    }

    fn range_eq(&self, other: &Self, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
        matches!(
            self.range_ord(other, arena),
            Some(std::cmp::Ordering::Equal)
        )
    }

    fn range_ord(
        &self,
        other: &Self,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<std::cmp::Ordering> {
        match self.len.range_ord(&other.len, arena) {
            Some(std::cmp::Ordering::Equal) => {
                let mut eq = 0;
                let mut self_lt = 0;
                let mut self_gt = 0;
                self.val.iter().zip(other.val.iter()).for_each(
                    |((self_key, self_val), (other_key, other_val))| {
                        if let Some(std::cmp::Ordering::Equal) =
                            self_key.clone().range_ord(other_key, arena)
                        {
                            match self_val.0.clone().range_ord(&other_val.0, arena) {
                                Some(std::cmp::Ordering::Equal) => eq += 1,
                                Some(std::cmp::Ordering::Less) => self_lt += 1,
                                Some(std::cmp::Ordering::Greater) => self_gt += 1,
                                _ => {}
                            }
                        }
                    },
                );

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
            other => other,
        }
    }

    fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        let mut deps: Vec<ContextVarNode> = self.len.dependent_on(analyzer, arena);
        deps.extend(
            self.val
                .iter()
                .flat_map(|(_, val)| val.0.dependent_on(analyzer, arena))
                .collect::<Vec<_>>(),
        );
        deps
    }

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        let mut deps: Vec<ContextVarNode> = self.len.recursive_dependent_on(analyzer, arena)?;
        deps.extend(
            self.val
                .values()
                .map(|val| val.0.recursive_dependent_on(analyzer, arena))
                .collect::<Result<Vec<Vec<_>>, _>>()?
                .iter()
                .flatten()
                .collect::<Vec<_>>(),
        );
        deps.extend(
            self.val
                .keys()
                .map(|key| key.recursive_dependent_on(analyzer, arena))
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
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let mut has_cycle = false;
        has_cycle = has_cycle || self.len.has_cycle(seen, analyzer, arena)?;
        self.val.iter().try_for_each(|(_, val)| {
            has_cycle = has_cycle || val.0.has_cycle(seen, analyzer, arena)?;
            Ok(())
        })?;
        Ok(has_cycle)
    }

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let mut deps_on = false;
        deps_on |= self.len.depends_on(var, seen, analyzer, arena)?;
        self.val.iter().try_for_each(|(_, val)| {
            deps_on |= val.0.depends_on(var, seen, analyzer, arena)?;
            Ok(())
        })?;
        Ok(deps_on)
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
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
            len: Box::new(self.len.flatten(maximize, analyzer, arena)?),
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(
                        idx.flatten(maximize, analyzer, arena)?,
                        (val.0.flatten(maximize, analyzer, arena)?, val.1),
                    );
                }
                map
            },
            op_num: self.op_num,
            loc: self.loc,
        }))
    }

    fn cache_flatten(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        if self.flattened_max.is_none() {
            self.len.cache_flatten(analyzer, arena)?;
            let mapping = std::mem::take(&mut self.val);
            self.val = mapping
                .into_iter()
                .map(|(mut idx, mut val)| {
                    idx.cache_flatten(analyzer, arena).unwrap();
                    val.0.cache_flatten(analyzer, arena).unwrap();
                    (idx, val)
                })
                .collect();
            let flat_max = self.flatten(true, analyzer, arena)?;
            let simplified_flat_max = flat_max.simplify_maximize(analyzer, arena)?;
            self.flattened_max = Some(Box::new(simplified_flat_max));
        }
        if self.flattened_min.is_none() {
            self.len.cache_flatten(analyzer, arena)?;
            let mapping = std::mem::take(&mut self.val);
            self.val = mapping
                .into_iter()
                .map(|(mut idx, mut val)| {
                    idx.cache_flatten(analyzer, arena).unwrap();
                    val.0.cache_flatten(analyzer, arena).unwrap();
                    (idx, val)
                })
                .collect();
            let flat_min = self.flatten(false, analyzer, arena)?;
            let simplified_flat_min = flat_min.simplify_minimize(analyzer, arena)?;
            self.flattened_min = Some(Box::new(simplified_flat_min));
        }
        Ok(())
    }

    fn is_flatten_cached(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        self.flattened_min.is_some() && self.flattened_max.is_some()
    }

    fn is_min_max_cached(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (bool, bool) {
        (self.minimized.is_some(), self.maximized.is_some())
    }

    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        self.len
            .filter_recursion(node_idx, new_idx, analyzer, arena);
        self.val = self
            .val
            .clone()
            .into_iter()
            .map(|(mut k, mut v)| {
                k.filter_recursion(node_idx, new_idx, analyzer, arena);
                v.0.filter_recursion(node_idx, new_idx, analyzer, arena);
                (k, v)
            })
            .collect();
    }

    fn maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.maximize(analyzer, arena)?,
            {
                let mut map: BTreeMap<_, (Elem<Concrete>, usize)> = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont maximize the key so that any subsequent
                    // `get_index` can find potential values
                    let maximized = val.0.maximize(analyzer, arena)?;
                    map.insert(idx.simplify_maximize(analyzer, arena)?, (maximized, val.1));
                }

                map
            },
            self.loc,
        )))
    }

    fn minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.minimize(analyzer, arena)?,
            {
                let mut map: BTreeMap<_, (Elem<Concrete>, usize)> = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let minimized = val.0.minimize(analyzer, arena)?;
                    map.insert(idx.simplify_minimize(analyzer, arena)?, (minimized, val.1));
                }

                map
            },
            self.loc,
        )))
    }

    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(max) = &self.flattened_max {
            return Ok(*max.clone());
        }
        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.simplify_maximize(analyzer, arena)?,
            {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let simplified = val.0.simplify_maximize(analyzer, arena)?;
                    map.insert(idx, (simplified, val.1));
                }
                map
            },
            self.loc,
        )))
    }
    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        if let Some(min) = &self.flattened_min {
            return Ok(*min.clone());
        }

        Ok(Elem::ConcreteDyn(Self::new_w_op_nums(
            self.len.simplify_minimize(analyzer, arena)?,
            {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    // We dont minimize the key so that any subsequent
                    // `get_index` can find potential values
                    let simplified = val.0.simplify_minimize(analyzer, arena)?;
                    map.insert(idx, (simplified, val.1));
                }
                map
            },
            self.loc,
        )))
    }

    fn cache_maximize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.len.cache_maximize(g, arena)?;
            let mapping = std::mem::take(&mut self.val);
            self.val = mapping
                .into_iter()
                .map(|(mut idx, mut val)| {
                    idx.cache_maximize(g, arena).unwrap();
                    val.0.cache_maximize(g, arena).unwrap();
                    (idx, val)
                })
                .collect();
            self.maximized = Some(MinMaxed::Maximized(Box::new(self.maximize(g, arena)?)));
        }
        Ok(())
    }

    fn cache_minimize(
        &mut self,
        g: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.len.cache_minimize(g, arena)?;
            let mapping = std::mem::take(&mut self.val);
            self.val = mapping
                .into_iter()
                .map(|(mut idx, mut val)| {
                    idx.cache_minimize(g, arena).unwrap();
                    val.0.cache_minimize(g, arena).unwrap();
                    (idx, val)
                })
                .collect();
            self.minimized = Some(MinMaxed::Minimized(Box::new(self.minimize(g, arena)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
    }
}
