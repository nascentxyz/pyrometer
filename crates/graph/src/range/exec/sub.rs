use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256, U256};

impl RangeSub<Concrete> for RangeConcrete<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let op_res = lhs_val.saturating_sub(rhs_val);
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    match self.val {
                        Concrete::Int(size, val) => {
                            let op_res = val.saturating_sub(I256::from_raw(rhs_val));
                            let val = Concrete::Int(size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                        _ => {
                            // TODO: this should cause a revert
                            let op_res = lhs_val.saturating_sub(rhs_val);
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let tmp = Concrete::Uint(*lhs_size, U256::zero());
                    let max = Concrete::max_of_type(&tmp).unwrap().uint_val().unwrap();

                    let op_res = val.saturating_add(neg_v.into_raw()).min(max);
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = neg_v.saturating_sub(I256::from_raw(*val).max(min));
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let op_res = l.saturating_sub(*r);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let op_res = lhs_val.overflowing_sub(rhs_val).0;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    match self.val {
                        Concrete::Int(size, val) => {
                            let op_res = val.overflowing_sub(I256::from_raw(rhs_val)).0;
                            let val = Concrete::Int(size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                        _ => {
                            let op_res = lhs_val.overflowing_sub(rhs_val).0;
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let op_res = val.overflowing_add(neg_v.into_raw()).0;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let op_res = I256::from_raw(neg_v.into_raw().overflowing_sub(*val).0);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => Some(Elem::Concrete(
                    RangeConcrete::new(Concrete::Int(*lhs_size, l.overflowing_sub(*r).0), self.loc),
                )),
                _ => None,
            },
        }
    }
}

impl RangeSub<Concrete> for Elem<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_sub(b),
            _ => None,
        }
    }

    fn range_wrapping_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_sub(b),
            _ => None,
        }
    }
}
