impl RangeMul<Concrete> for RangeConcrete<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max(&self.val).unwrap();
                let res = lhs_val
                    .saturating_mul(rhs_val)
                    .min(max.into_u256().unwrap());
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(res),
                    loc: self.loc,
                }))
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let max = if *lhs_size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - I256::from(1)
                    };
                    let min = max * I256::from(-1i32) - I256::from(1i32);
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            neg_v.saturating_mul(I256::from_raw(*val)).max(min),
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let max = if *lhs_size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - I256::from(1)
                    };
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, l.saturating_mul(*r).min(max)),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let _max = Concrete::max(&self.val).unwrap();
                let res = lhs_val.overflowing_mul(rhs_val).0;
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(res),
                    loc: self.loc,
                }))
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            neg_v.overflowing_mul(I256::from_raw(*val)).0,
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, l.overflowing_mul(*r).0),
                        loc: self.loc,
                    }))
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
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            (Elem::Concrete(a), b) if a.val.into_u256() == Some(U256::from(1)) => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::from(1)) => Some(a.clone()),
            _ => None,
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_mul(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            (Elem::Concrete(a), b) if a.val.into_u256() == Some(U256::from(1)) => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::from(1)) => Some(a.clone()),
            _ => None,
        }
    }
}