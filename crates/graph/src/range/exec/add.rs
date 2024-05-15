use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256, U256};

impl RangeAdd<Concrete> for RangeConcrete<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                // `max_of_type` cannot fail on uint
                let max_uint = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .into_u256()
                    .unwrap();
                // min { a + b, max } to cap at maximum of lhs sizing
                let res = lhs_val.saturating_add(rhs_val).min(max_uint);
                let ret_val = self.val.u256_as_original(res);
                let rc = RangeConcrete::new(ret_val, self.loc);
                Some(rc.into())
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        // neg_v guaranteed to be negative here
                        let abs = neg_v.into_raw();
                        if abs > *val {
                            // -b + a
                            let res = neg_v.saturating_add(I256::from_raw(*val));
                            let ret_val = Concrete::Int(*lhs_size, res);
                            let rc = RangeConcrete::new(ret_val, self.loc);
                            Some(rc.into())
                        } else {
                            // a - |b|
                            let res = val.saturating_sub(abs);
                            let ret_val = self.val.u256_as_original(res);
                            let rc = RangeConcrete::new(ret_val, self.loc);
                            Some(rc.into())
                        }
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        // `min_of_type` cannot fail on int
                        let min = Concrete::min_of_type(&self.val).unwrap().int_val().unwrap();
                        // lhs + rhs when both are negative is effectively lhs - rhs which means
                        // we saturate at the minimum value of the left hand side.
                        // therefore, max{ l + r, min } is the result
                        let val = Concrete::Int(*lhs_size, l.saturating_add(*r).max(min));
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                    _ => None,
                }
            }
        }
    }

    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let res = lhs_val.overflowing_add(rhs_val).0;
                let ret_val = self.val.u256_as_original(res);
                let rc = RangeConcrete::new(ret_val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let res = I256::from_raw(neg_v.into_raw().overflowing_add(*val).0);
                    let ret_val = Concrete::Int(*lhs_size, res);
                    let rc = RangeConcrete::new(ret_val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let res = l.overflowing_add(*r).0;
                    let ret_val = Concrete::Int(*lhs_size, res);
                    let rc = RangeConcrete::new(ret_val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeAdd<Concrete> for Elem<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(other.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_add(b),
            _ => None,
        }
    }
    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(other.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_add(b),
            _ => None,
        }
    }
}
