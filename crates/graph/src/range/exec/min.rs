use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

impl RangeMin<Concrete> for RangeConcrete<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.min(rhs_val);
                let res = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(res, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, _), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, _)) => {
                    let res = Concrete::Int(*lhs_size, *neg_v);
                    let rc = RangeConcrete::new(res, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let res = Concrete::Int(*lhs_size, *l.min(r));
                    let rc = RangeConcrete::new(res, self.loc);
                    Some(rc.into())
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
            }
            (c @ Elem::Concrete(_), Elem::ConcreteDyn(b))
            | (Elem::ConcreteDyn(b), c @ Elem::Concrete(_)) => {
                if b.op_num == 0 {
                    Some(c.clone())
                } else {
                    None
                }
            }
            (_, Elem::Null) => Some(self.clone()),
            (Elem::Null, _) => Some(other.clone()),
            _ => None,
        }
    }
}
