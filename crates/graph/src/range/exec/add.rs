use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256, U256};

impl RangeAdd<Concrete> for RangeConcrete<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max(&self.val).unwrap();
                let max_uint = max.into_u256().unwrap();
                Some(Elem::Concrete(RangeConcrete {
                    val: self
                        .val
                        .u256_as_original(lhs_val.saturating_add(rhs_val).min(max_uint)),
                    loc: self.loc,
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        // neg_v guaranteed to be negative here
                        if neg_v.into_raw() > *val {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(
                                    *lhs_size,
                                    neg_v.saturating_add(I256::from_raw(*val)),
                                ),
                                loc: self.loc,
                            }))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: self
                                    .val
                                    .u256_as_original(val.saturating_sub(neg_v.into_raw())),
                                loc: self.loc,
                            }))
                        }
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1))
                                - I256::from(1)
                        };
                        let min = max * I256::from(-1i32) - I256::from(1i32);
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, l.saturating_add(*r).max(min)),
                            loc: self.loc,
                        }))
                    }
                    _ => None,
                }
            }
        }
    }
    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self
                    .val
                    .u256_as_original(lhs_val.overflowing_add(rhs_val).0),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            I256::from_raw(neg_v.into_raw().overflowing_add(*val).0),
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, l.overflowing_add(*r).0),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeAdd<Concrete> for Elem<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_add(b),
            _ => None,
        }
    }
    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_add(b),
            _ => None,
        }
    }
}
