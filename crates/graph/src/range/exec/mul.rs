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
                let res = lhs_val.saturating_mul(rhs_val).min(max);
                let res_val = self.val.u256_as_original(res);
                let rc = RangeConcrete::new(res_val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();

                    let res = neg_v.saturating_mul(I256::from_raw(*val)).max(min);
                    let res_val = Concrete::Int(*lhs_size, res);
                    let rc = RangeConcrete::new(res_val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let res = l.saturating_mul(*r).min(max);
                    let res_val = Concrete::Int(*lhs_size, res);
                    let rc = RangeConcrete::new(res_val, self.loc);
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
                let res = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(res, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let op_res = neg_v.overflowing_mul(I256::from_raw(*val)).0;
                    let res = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(res, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let res = Concrete::Int(*lhs_size, l.overflowing_mul(*r).0);
                    let rc = RangeConcrete::new(res, self.loc);
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
