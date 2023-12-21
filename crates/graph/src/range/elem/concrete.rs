use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{Elem, RangeElem},
    GraphBackend, GraphError,
};

use shared::NodeIdx;

use std::collections::BTreeMap;

use solang_parser::pt::Loc;

/// A concrete value for a range element
#[derive(Default, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeConcrete<T> {
    pub val: T,
    pub loc: Loc,
}

impl From<Concrete> for RangeConcrete<Concrete> {
    fn from(c: Concrete) -> Self {
        Self {
            val: c,
            loc: Loc::Implicit,
        }
    }
}

impl RangeConcrete<Concrete> {
    pub fn as_bytes(&self, _analyzer: &impl GraphBackend, _maximize: bool) -> Option<Vec<u8>> {
        Some(self.val.as_bytes())
    }
}

impl RangeElem<Concrete> for RangeConcrete<Concrete> {
    type GraphError = GraphError;
    fn arenaize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        let _ = analyzer.range_arena_idx_or_upsert(Elem::Concrete(self.clone()));
        Ok(())
    }

    fn has_cycle(
        &self,
        _seen: &mut Vec<ContextVarNode>,
        _analyzer: &impl GraphBackend,
    ) -> Result<bool, Self::GraphError> {
        Ok(false)
    }

    fn flatten(
        &self,
        _maximize: bool,
        _analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn is_flatten_cached(&self, _analyzer: &impl GraphBackend) -> bool {
        true
    }

    fn cache_flatten(&mut self, _: &mut impl GraphBackend) -> Result<(), GraphError> {
        Ok(())
    }

    fn range_eq(&self, other: &Self, analyzer: &impl GraphBackend) -> bool {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(self_val), Some(other_val)) => self_val == other_val,
            _ => match (&self.val, &other.val) {
                (Concrete::Int(_, s), Concrete::Int(_, o)) => s == o,
                (Concrete::DynBytes(s), Concrete::DynBytes(o)) => s == o,
                (Concrete::String(s), Concrete::String(o)) => s == o,
                (Concrete::DynBytes(s), Concrete::String(o)) => s == o.as_bytes(),
                (Concrete::String(s), Concrete::DynBytes(o)) => s.as_bytes() == o,
                (Concrete::Array(a), Concrete::Array(b)) => {
                    if a.len() == b.len() {
                        a.iter().zip(b.iter()).all(|(a, b)| {
                            let a = RangeConcrete {
                                val: a.clone(),
                                loc: self.loc,
                            };

                            let b = RangeConcrete {
                                val: b.clone(),
                                loc: other.loc,
                            };

                            a.range_eq(&b, analyzer)
                        })
                    } else {
                        false
                    }
                }
                _ => false,
            },
        }
    }

    fn range_ord(&self, other: &Self, _analyzer: &impl GraphBackend) -> Option<std::cmp::Ordering> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(self_val), Some(other_val)) => Some(self_val.cmp(&other_val)),
            (Some(_), _) => {
                match other.val {
                    Concrete::Int(_, _) => {
                        // if we couldnt convert an int to uint, its negative
                        // so self must be > other
                        Some(std::cmp::Ordering::Greater)
                    }
                    _ => None,
                }
            }
            (_, Some(_)) => {
                match self.val {
                    Concrete::Int(_, _) => {
                        // if we couldnt convert an int to uint, its negative
                        // so self must be < other
                        Some(std::cmp::Ordering::Less)
                    }
                    _ => None,
                }
            }
            _ => {
                match (&self.val, &other.val) {
                    // two negatives
                    (Concrete::Int(_, s), Concrete::Int(_, o)) => Some(s.cmp(o)),
                    (Concrete::DynBytes(b0), Concrete::DynBytes(b1)) => Some(b0.cmp(b1)),
                    _ => None,
                }
            }
        }
    }

    fn dependent_on(&self, _analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        vec![]
    }

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx, _analyzer: &mut impl GraphBackend) {}

    fn maximize(&self, _analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn minimize(&self, _analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn simplify_maximize(
        &self,
        _seen_ops: &mut BTreeMap<Elem<Concrete>, Elem<Concrete>>,
        _analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn simplify_minimize(
        &self,
        _seen_ops: &mut BTreeMap<Elem<Concrete>, Elem<Concrete>>,
        _analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn cache_maximize(&mut self, _g: &mut impl GraphBackend) -> Result<(), GraphError> {
        Ok(())
    }

    fn cache_minimize(&mut self, _g: &mut impl GraphBackend) -> Result<(), GraphError> {
        Ok(())
    }
    fn uncache(&mut self) {}

    fn recursive_dependent_on(
        &self,
        _: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        Ok(vec![])
    }
}
