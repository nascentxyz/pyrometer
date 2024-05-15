use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use ethers_core::types::U256;

impl RangeExp<Concrete> for RangeConcrete<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max_of_type(&self.val).unwrap();

                let op_res = lhs_val.checked_pow(rhs_val);
                let res = if let Some(num) = op_res {
                    num.min(max.into_u256().unwrap())
                } else {
                    max.into_u256().unwrap()
                };

                let res_val = self.val.u256_as_original(res);
                let rc = RangeConcrete::new(res_val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let pow2 = val % U256::from(2) == 0.into();
                    let res = if val > &U256::from(u32::MAX) {
                        if pow2 {
                            Concrete::max_of_type(&self.val).unwrap()
                        } else {
                            Concrete::min_of_type(&self.val).unwrap()
                        }
                    } else {
                        let min = Concrete::min_of_type(&self.val).unwrap().int_val().unwrap();
                        let max = Concrete::max_of_type(&self.val).unwrap().int_val().unwrap();

                        let op_res = neg_v.checked_pow(val.as_u32());
                        if let Some(num) = op_res {
                            if pow2 {
                                Concrete::Int(*lhs_size, num.min(max))
                            } else {
                                Concrete::Int(*lhs_size, num.max(min))
                            }
                        } else if pow2 {
                            Concrete::max_of_type(&self.val).unwrap()
                        } else {
                            Concrete::min_of_type(&self.val).unwrap()
                        }
                    };
                    let rc = RangeConcrete::new(res, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeExp<Concrete> for Elem<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_exp(b),
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(Concrete::from(U256::from(1)).into()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(other.clone()),
            _ => None,
        }
    }
}
