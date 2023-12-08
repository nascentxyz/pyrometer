impl RangeSub<Concrete> for RangeConcrete<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let val = lhs_val.saturating_sub(rhs_val);
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(val),
                        loc: self.loc,
                    }))
                } else {
                    match self.val {
                        Concrete::Int(size, val) => Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(size, val.saturating_sub(I256::from_raw(rhs_val))),
                            loc: self.loc,
                        })),
                        _ => {
                            // TODO: this should cause a revert
                            let val = lhs_val.saturating_sub(rhs_val);
                            Some(Elem::Concrete(RangeConcrete {
                                val: self.val.u256_as_original(val),
                                loc: self.loc,
                            }))
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let max = if *lhs_size == 256 {
                        U256::MAX
                    } else {
                        U256::from(2).pow(U256::from(*lhs_size)) - 1
                    };
                    Some(Elem::Concrete(RangeConcrete {
                        val: self
                            .val
                            .u256_as_original(val.saturating_add(neg_v.into_raw()).min(max)),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let max = if *lhs_size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - I256::from(1)
                    };

                    let min = max * I256::from(-1i32) - I256::from(1i32);

                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            neg_v.saturating_sub(I256::from_raw(*val).max(min)),
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, l.saturating_sub(*r)),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let val = lhs_val.overflowing_sub(rhs_val).0;
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(val),
                        loc: self.loc,
                    }))
                } else {
                    match self.val {
                        Concrete::Int(size, val) => Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(
                                size,
                                val.overflowing_sub(I256::from_raw(rhs_val)).0,
                            ),
                            loc: self.loc,
                        })),
                        _ => {
                            let val = lhs_val.overflowing_sub(rhs_val).0;
                            Some(Elem::Concrete(RangeConcrete {
                                val: self.val.u256_as_original(val),
                                loc: self.loc,
                            }))
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, val), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self
                            .val
                            .u256_as_original(val.overflowing_add(neg_v.into_raw()).0),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            I256::from_raw(neg_v.into_raw().overflowing_sub(*val).0),
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, l.overflowing_sub(*r).0),
                        loc: self.loc,
                    }))
                }
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