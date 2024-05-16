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
                    let op_res = lhs_val / rhs_val;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    // Divisor cannot be zero because it would have been converted
                    // to a uint
                    let abs = neg_v.into_sign_and_abs().1;
                    let op_res = I256::from_raw(val / abs).saturating_mul(I256::from(-1i32));
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::from(0) {
                        None
                    } else {
                        let abs = neg_v.into_sign_and_abs().1;
                        let op_res = I256::from_raw(abs / *val).saturating_mul(I256::from(-1i32));
                        let val = Concrete::Int(*lhs_size, op_res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::from(0) {
                        None
                    } else {
                        let (op_res, overflow) = l.overflowing_div(*r);
                        if overflow {
                            let max = Concrete::max_of_type(&self.val).unwrap().int_val().unwrap();
                            let val = Concrete::Int(*lhs_size, max);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        } else {
                            let val = Concrete::Int(*lhs_size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        // Only negative Int / negative Int needs overflowing_div
        match (&self.val, &other.val) {
            (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r))
                if *l < I256::from(0i32) && *r < I256::from(0i32) =>
            {
                let op_res = l.overflowing_div(*r).0;
                let val = Concrete::Int(*lhs_size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => self.range_div(other),
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

#[cfg(test)]
mod tests {
    use super::*;
    use solang_parser::pt::Loc;

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(3)));
    }

    #[test]
    fn uint_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(5i32)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(3)));
    }

    #[test]
    fn uint_neg_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-3i32)));
    }

    #[test]
    fn neg_int_uint() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-3i32)));
    }

    #[test]
    fn neg_int_neg_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(3i32)));
    }

    #[test]
    fn uint_zero() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(0)), Loc::Implicit);
        assert!(x.range_div(&y).is_none());
    }

    #[test]
    fn int_zero() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(0)), Loc::Implicit);
        assert!(x.range_div(&y).is_none());
    }

    #[test]
    fn wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_wrapping_div(&y).unwrap();
        let expected = x.clone();
        assert_eq!(result, expected.into());
    }

    #[test]
    fn nonwrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }
}
