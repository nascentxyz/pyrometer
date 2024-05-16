use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::I256;

impl RangeMul<Concrete> for RangeConcrete<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .into_u256()
                    .unwrap();
                let mut op_res = lhs_val.saturating_mul(rhs_val).min(max);
                if let Some(min) = Concrete::min_of_type(&self.val).unwrap().into_u256() {
                    op_res = op_res.max(min);
                }
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = neg_v.saturating_mul(I256::from_raw(*val)).max(min).min(max);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = l.saturating_mul(*r).min(max).max(min);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.overflowing_mul(rhs_val).0;
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let op_res = neg_v.overflowing_mul(I256::from_raw(*val)).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let op_res = l.overflowing_mul(*r).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeMul<Concrete> for Elem<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mul(b),
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(other.clone()),
            (Elem::Concrete(a), b) if a.val.is_one() => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.is_one() => Some(a.clone()),
            _ => None,
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_mul(b),
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(other.clone()),
            (Elem::Concrete(a), b) if a.val.is_one() => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.is_one() => Some(a.clone()),
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
    fn sized_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn sized_wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(1)));
    }

    #[test]
    fn sized_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(127i32)));
    }

    #[test]
    fn sized_int_uint() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(127i32)), Loc::Implicit);
        let y2 = RangeConcrete::new(Concrete::Uint(8, U256::from(127)), Loc::Implicit);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        let result2 = x.range_mul(&y2).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }
    #[test]
    fn sized_uint_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(127i32)), Loc::Implicit);
        let x2 = RangeConcrete::new(Concrete::Uint(8, U256::from(127)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        let result2 = x2.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn sized_wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(1i32)));
    }

    #[test]
    fn sized_wrapping_int_uint() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(127i32)), Loc::Implicit);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        let y2 = RangeConcrete::new(Concrete::Uint(8, U256::from(127i32)), Loc::Implicit);
        let result2 = x
            .range_wrapping_mul(&y2)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-1i32)));
    }
}
