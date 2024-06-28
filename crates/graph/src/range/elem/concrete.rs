use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{Elem, RangeArenaLike, RangeElem},
    GraphBackend,
};

use shared::{GraphError, NodeIdx, RangeArena};

use std::hash::{Hash, Hasher};

use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;

/// A concrete value for a range element
#[derive(Default, Clone, Debug, Ord, PartialOrd)]
pub struct RangeConcrete<T> {
    /// The value of the concrete
    pub val: T,
    /// The source code location
    pub loc: Loc,
}

pub fn rc_uint_sized(n: u128) -> RangeConcrete<Concrete> {
    let size: u16 = ((32 - ((n.leading_zeros() + 128) / 8)) * 8).max(8) as u16;
    RangeConcrete::new(Concrete::Uint(size, U256::from(n)), Loc::Implicit)
}

pub fn rc_uint256(n: u128) -> RangeConcrete<Concrete> {
    RangeConcrete::new(Concrete::Uint(256, U256::from(n)), Loc::Implicit)
}

pub fn rc_int_sized(n: i128) -> RangeConcrete<Concrete> {
    let size: u16 = ((32 - ((n.abs().leading_zeros() + 128) / 8)) * 8).max(8) as u16;
    RangeConcrete::new(Concrete::Int(size, I256::from(n)), Loc::Implicit)
}

pub fn rc_i256_sized(n: I256) -> RangeConcrete<Concrete> {
    let size: u16 = ((32 - ((n.abs().leading_zeros()) / 8)) * 8).max(8) as u16;
    RangeConcrete::new(Concrete::Int(size, n), Loc::Implicit)
}

pub fn rc_int256(n: i128) -> RangeConcrete<Concrete> {
    RangeConcrete::new(Concrete::Int(256, I256::from(n)), Loc::Implicit)
}

impl<T> RangeConcrete<T> {
    pub fn new(val: T, loc: Loc) -> Self {
        Self { val, loc }
    }
}

impl<T: std::cmp::PartialEq> PartialEq for RangeConcrete<T> {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.val
    }
}
impl<T: std::cmp::PartialEq> Eq for RangeConcrete<T> {}

impl<T: Hash> Hash for RangeConcrete<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.val.hash(state);
    }
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
    pub fn as_bytes(
        &self,
        _analyzer: &impl GraphBackend,
        _maximize: bool,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<Vec<u8>> {
        Some(self.val.as_bytes())
    }
}

impl RangeElem<Concrete> for RangeConcrete<Concrete> {
    type GraphError = GraphError;
    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let _ = arena.idx_or_upsert(Elem::Concrete(self.clone()), analyzer);
        Ok(())
    }

    fn has_cycle(
        &self,
        _seen: &mut Vec<ContextVarNode>,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, Self::GraphError> {
        Ok(false)
    }

    fn depends_on(
        &self,
        _var: ContextVarNode,
        _seen: &mut Vec<ContextVarNode>,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, Self::GraphError> {
        Ok(false)
    }

    fn flatten(
        &self,
        _maximize: bool,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn is_flatten_cached(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> bool {
        true
    }

    fn is_min_max_cached(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> (bool, bool) {
        (true, true)
    }

    fn cache_flatten(
        &mut self,
        _: &mut impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        Ok(())
    }

    fn range_eq(&self, other: &Self, arena: &mut RangeArena<Elem<Concrete>>) -> bool {
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
                            let a = RangeConcrete::new(a.clone(), self.loc);

                            let b = RangeConcrete::new(b.clone(), other.loc);

                            a.range_eq(&b, arena)
                        })
                    } else {
                        false
                    }
                }
                _ => false,
            },
        }
    }

    fn range_ord(
        &self,
        other: &Self,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Option<std::cmp::Ordering> {
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

    fn dependent_on(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<ContextVarNode> {
        vec![]
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
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn minimize(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn simplify_maximize(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn simplify_minimize(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn cache_maximize(
        &mut self,
        _g: &mut impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        Ok(())
    }

    fn cache_minimize(
        &mut self,
        _g: &mut impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        Ok(())
    }
    fn uncache(&mut self) {}

    fn recursive_dependent_on(
        &self,
        _: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        Ok(vec![])
    }
}
