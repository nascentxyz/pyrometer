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
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => {
                if a.op_num > b.op_num {
                    Some(self.clone())
                } else if a.op_num < b.op_num {
                    Some(other.clone())
                } else {
                    None
                }
            },
            (c @ Elem::Concrete(_), Elem::ConcreteDyn(b))
            | (Elem::ConcreteDyn(b), c @ Elem::Concrete(_)) => {
                if b.op_num == 0 {
                    Some(c.clone())
                } else {
                    None
                }
            },
            (_, Elem::Null) => Some(self.clone()),
            (Elem::Null, _) => Some(other.clone()),
            _ => None,
        }
    }
}
