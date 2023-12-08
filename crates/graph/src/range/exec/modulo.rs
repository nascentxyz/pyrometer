use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256};

impl RangeMod<Concrete> for RangeConcrete<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val % rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, I256::from_raw(*val) % *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v % I256::from_raw(*val)),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l % *r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeMod<Concrete> for Elem<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mod(b),
            _ => None,
        }
    }
}
