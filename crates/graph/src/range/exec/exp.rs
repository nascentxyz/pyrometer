use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use ethers_core::types::U256;

impl RangeExp<Concrete> for RangeConcrete<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max(&self.val).unwrap();
                if let Some(num) = lhs_val.checked_pow(rhs_val) {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(num.min(max.into_u256().unwrap())),
                        loc: self.loc,
                    }))
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(max.into_u256().unwrap()),
                        loc: self.loc,
                    }))
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let pow2 = val % U256::from(2) == 0.into();
                    if val > &U256::from(u32::MAX) {
                        if pow2 {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::max(&self.val).unwrap(),
                                loc: self.loc,
                            }))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::min(&self.val).unwrap(),
                                loc: self.loc,
                            }))
                        }
                    } else {
                        let min = Concrete::min(&self.val).unwrap().int_val().unwrap();
                        let max = Concrete::max(&self.val).unwrap().int_val().unwrap();

                        if let Some(num) = neg_v.checked_pow(val.as_u32()) {
                            if pow2 {
                                Some(Elem::Concrete(RangeConcrete {
                                    val: Concrete::Int(*lhs_size, num.min(max)),
                                    loc: self.loc,
                                }))
                            } else {
                                Some(Elem::Concrete(RangeConcrete {
                                    val: Concrete::Int(*lhs_size, num.max(min)),
                                    loc: self.loc,
                                }))
                            }
                        } else if pow2 {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::max(&self.val).unwrap(),
                                loc: self.loc,
                            }))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::min(&self.val).unwrap(),
                                loc: self.loc,
                            }))
                        }
                    }
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
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => {
                Some(Elem::from(Concrete::from(U256::from(1))))
            }
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            _ => None,
        }
    }
}