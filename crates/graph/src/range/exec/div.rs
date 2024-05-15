use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256, U256};

impl RangeDiv<Concrete> for RangeConcrete<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == 0.into() {
                    None
                } else {
                    let val = self.val.u256_as_original(lhs_val / rhs_val);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    if neg_v == &I256::from(0) {
                        None
                    } else {
                        let res = I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32);
                        let val = Concrete::Int(*lhs_size, res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::from(0) {
                        None
                    } else {
                        let res = *neg_v / I256::from_raw(*val);
                        let val = Concrete::Int(*lhs_size, res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::from(0) {
                        None
                    } else {
                        let (val, overflow) = l.overflowing_div(*r);
                        if overflow {
                            None
                        } else {
                            let res = Concrete::Int(*lhs_size, val);
                            let rc = RangeConcrete::new(res, self.loc);
                            Some(rc.into())
                        }
                    }
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let val = if rhs_val == 0.into() {
                    self.val.u256_as_original(U256::zero())
                } else {
                    self.val.u256_as_original(lhs_val / rhs_val)
                };
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let val = if neg_v == &I256::from(0) {
                        Concrete::Int(*lhs_size, I256::from(0i32))
                    } else {
                        let res = I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32);
                        Concrete::Int(*lhs_size, res)
                    };

                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let val = if val == &U256::from(0) {
                        Concrete::Int(*lhs_size, I256::from(0i32))
                    } else {
                        let res = *neg_v / I256::from_raw(*val);
                        Concrete::Int(*lhs_size, res)
                    };
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::from(0) {
                        let ret_val = Concrete::Int(*lhs_size, I256::from(0i32));
                        let rc = RangeConcrete::new(ret_val, self.loc);
                        Some(rc.into())
                    } else {
                        let (val, overflow) = l.overflowing_div(*r);
                        if overflow {
                            None
                        } else {
                            let ret_val = Concrete::Int(*lhs_size, val);
                            let rc = RangeConcrete::new(ret_val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
                _ => None,
            },
        }
    }
}

impl RangeDiv<Concrete> for Elem<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_div(b),
            _ => None,
        }
    }

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_div(b),
            _ => None,
        }
    }
}
