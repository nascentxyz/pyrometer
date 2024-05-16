use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::I256;

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
                let op_res = lhs_val.saturating_add(rhs_val).min(max_uint);
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        // neg_v guaranteed to be negative here
                        let abs = neg_v.abs().into_raw();
                        if abs > *val {
                            // |b| - a
                            let op_res =
                                I256::from_raw(abs.saturating_sub(*val)) * I256::from(-1i32);
                            let val = Concrete::Int(*lhs_size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        } else {
                            // a - |b|
                            let op_res = val.saturating_sub(abs);
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        // `min_of_type` cannot fail on int
                        let min = Concrete::min_of_type(&self.val).unwrap().int_val().unwrap();
                        // lhs + rhs when both are negative is effectively lhs - rhs which means
                        // we saturate at the minimum value of the left hand side.
                        // therefore, max{ l + r, min } is the result
                        let op_res = l.saturating_add(*r).max(min);
                        let val = Concrete::Int(*lhs_size, op_res);
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
                let op_res = lhs_val.overflowing_add(rhs_val).0;
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(..), Concrete::Int(..))
                | (Concrete::Int(..), Concrete::Uint(..)) => {
                    // just fall back to normal implementation because
                    // a positive and negative cannot overflow in addition
                    self.range_add(other)
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let op_res = l.overflowing_add(*r).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
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

#[cfg(test)]
mod tests {
    use super::*;
    use ethers_core::types::U256;
    use solang_parser::pt::Loc;

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(20)));
    }

    #[test]
    fn saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX));
    }

    #[test]
    fn sized_saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn int_big_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(14)));
    }

    #[test]
    fn big_int_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-14i32)));
    }

    #[test]
    fn int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-30i32)));
    }

    #[test]
    fn saturating_int_int() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::MIN + I256::from(1i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-2i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MIN));
    }

    #[test]
    fn sized_saturating_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-2i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(2)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(1)));
    }

    #[test]
    fn sized_wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(2)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(1)));
    }

    #[test]
    fn wrapping_big_int_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-14i32)));
    }

    #[test]
    fn wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn sized_wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-128i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(127i32)));
    }
}
