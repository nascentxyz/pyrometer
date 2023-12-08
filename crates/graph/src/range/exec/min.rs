use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

impl RangeMin<Concrete> for RangeConcrete<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val.min(rhs_val)),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, _), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l.min(r)),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeMin<Concrete> for Elem<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_min(b),
            _ => None,
        }
    }
}