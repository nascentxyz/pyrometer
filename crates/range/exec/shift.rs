pub trait RangeShift<T, Rhs = Self> {
    /// Perform a bitwise shift left
    fn range_shl(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise shift right
    fn range_shr(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeShift<Concrete> for RangeConcrete<Concrete> {
    fn range_shl(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val > 256.into() {
                    return Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(U256::zero()),
                        loc: self.loc,
                    }));
                }
                let max = Concrete::max(&self.val).unwrap().into_u256().unwrap();
                if self.val.int_val().is_some() {
                    // ints get weird treatment because they can push into the negatives
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            self.val.int_size().unwrap(),
                            I256::from_raw(lhs_val << rhs_val),
                        ),
                        loc: self.loc,
                    }))
                } else if rhs_val > lhs_val.leading_zeros().into() {
                    Some(Elem::Concrete(RangeConcrete {
                        val: max.into(),
                        loc: self.loc,
                    }))
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original((lhs_val << rhs_val).min(max)),
                        loc: self.loc,
                    }))
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::zero() {
                        return Some(Elem::Concrete(self.clone()));
                    }

                    let max = if *lhs_size == 256 {
                        I256::MAX
                    } else {
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - I256::from(1)
                    };

                    let min = max * I256::from(-1i32) - I256::from(1i32);
                    let (abs, is_min) = neg_v.overflowing_abs();
                    if is_min {
                        if val > &U256::zero() {
                            Some(Elem::from(self.clone()))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(*lhs_size, I256::zero()),
                                loc: self.loc,
                            }))
                        }
                    } else if val > &U256::from(abs.leading_zeros()) {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::zero()),
                            loc: self.loc,
                        }))
                    } else {
                        let raw = I256::from_raw(abs.into_raw() << val);
                        let as_int = if raw == I256::MIN {
                            raw
                        } else {
                            I256::from(-1i32) * raw
                        };
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, as_int.max(min)),
                            loc: self.loc,
                        }))
                    }
                }
                _ => None,
            },
        }
    }

    fn range_shr(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == U256::zero() {
                    Some(Elem::Concrete(self.clone()))
                } else if rhs_val > U256::from(256) {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(U256::zero()),
                        loc: self.loc,
                    }))
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(lhs_val >> rhs_val),
                        loc: self.loc,
                    }))
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::zero() {
                        Some(Elem::Concrete(self.clone()))
                    } else if val > &U256::from(*lhs_size) {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from(-1i32)),
                            loc: self.loc,
                        }))
                    } else {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1))
                                - I256::from(1)
                        };
                        let min = max * I256::from(-1i32) - I256::from(1i32);

                        let (abs, is_min) = neg_v.overflowing_abs();
                        let bits = if is_min {
                            255
                        } else {
                            255 - abs.leading_zeros()
                        };

                        if val >= &U256::from(bits) {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(*lhs_size, I256::from(-1i32)),
                                loc: self.loc,
                            }))
                        } else {
                            let shr_val = abs.into_raw() >> val;
                            let as_int = I256::from_raw(shr_val);
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(
                                    *lhs_size,
                                    (I256::from(-1i32) * as_int).max(min),
                                ),
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

impl RangeShift<Concrete> for Elem<Concrete> {
    fn range_shl(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_shl(b),
            _ => None,
        }
    }
    fn range_shr(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_shr(b),
            _ => None,
        }
    }
}
