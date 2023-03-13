use crate::range::Elem;
use crate::range::RangeConcrete;
use crate::range::RangeDyn;
use crate::Concrete;
use ethers_core::types::H256;
use ethers_core::types::I256;
use ethers_core::types::U256;
use std::collections::BTreeMap;

pub trait RangeAdd<T, Rhs = Self> {
    /// Perform addition between two range elements
    fn range_add(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeAdd<Concrete> for RangeConcrete<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max(&self.val).unwrap().into_u256().unwrap();
                Some(Elem::Concrete(RangeConcrete {
                    val: self
                        .val
                        .u256_as_original(lhs_val.saturating_add(rhs_val).min(max)),
                    loc: self.loc,
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        // neg_v guaranteed to be negative here
                        if neg_v.into_raw() > *val {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(
                                    *lhs_size,
                                    neg_v.saturating_add(I256::from_raw(*val)),
                                ),
                                loc: self.loc,
                            }))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: self
                                    .val
                                    .u256_as_original(val.saturating_sub(neg_v.into_raw())),
                                loc: self.loc,
                            }))
                        }
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
                        let min = max * I256::from(-1i32);
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, l.saturating_add(*r).max(min)),
                            loc: self.loc,
                        }))
                    }
                    _ => None,
                }
            }
        }
    }
}

impl RangeAdd<Concrete> for Elem<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_add(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            _ => None,
        }
    }
}

pub trait RangeSub<T, Rhs = Self> {
    /// Perform subtraction between two range elements
    fn range_sub(&self, other: &Rhs) -> Option<Elem<T>>;
}

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
                        Concrete::Int(size, val) => {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(size, val.saturating_sub(I256::from_raw(rhs_val))),
                                loc: self.loc,
                            }))
                        },
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
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                    };

                    let min = max * I256::from(-1i32);

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
}

impl RangeSub<Concrete> for Elem<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_sub(b),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            _ => None,
        }
    }
}

pub trait RangeMul<T, Rhs = Self> {
    /// Perform multiplication between two range elements
    fn range_mul(&self, other: &Rhs) -> Option<Elem<T>>;
}

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
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                    };
                    let min = max * I256::from(-1i32);
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
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
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
}

impl RangeMul<Concrete> for Elem<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mul(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => {
                Some(other.clone())
            }
            _ => None,
        }
    }
}

pub trait RangeExp<T, Rhs = Self> {
    /// Perform exponentiation between two range elements
    fn range_exp(&self, other: &Rhs) -> Option<Elem<T>>;
}

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
pub trait RangeDiv<T, Rhs = Self> {
    /// Perform division between two range elements
    fn range_div(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeDiv<Concrete> for RangeConcrete<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val / rhs_val),
                    loc: self.loc,
                }))
            },
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(
                            *lhs_size,
                            I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32),
                        ),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v / I256::from_raw(*val)),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l / *r),
                        loc: self.loc,
                    }))
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
}

pub trait RangeMod<T, Rhs = Self> {
    /// Perform modulo between two range elements
    fn range_mod(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMod<Concrete> for RangeConcrete<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val % rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, I256::from_raw(*val) % *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v % I256::from_raw(*val)),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l % *r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeMod<Concrete> for Elem<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mod(b),
            _ => None,
        }
    }
}

pub trait RangeMin<T, Rhs = Self> {
    /// Take the minimum of two range elements
    fn range_min(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMin<Concrete> for RangeConcrete<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val.min(rhs_val)),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, _), Concrete::Int(_, neg_v)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *neg_v),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l.min(r)),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeMin<Concrete> for Elem<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_min(b),
            _ => None,
        }
    }
}

pub trait RangeMax<T, Rhs = Self> {
    /// Take the maximum of two range elements
    fn range_max(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMax<Concrete> for RangeConcrete<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val.max(rhs_val)),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(*lhs_size, *val),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, _), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(*lhs_size, *val),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l.max(r)),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeMax<Concrete> for Elem<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_max(b),
            _ => None,
        }
    }
}

pub trait RangeOrd<T, Rhs = Self> {
    /// Perform a logical equality test
    fn range_ord_eq(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical inequality test
    fn range_neq(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical greater than test
    fn range_gt(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical less than test
    fn range_lt(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical greater than or equal test
    fn range_gte(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical less than or equal test
    fn range_lte(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeOrd<Concrete> for RangeConcrete<Concrete> {
    fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val == rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l == r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val != rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l != r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val > rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l > r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val < rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l < r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val >= rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l >= r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val <= rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l <= r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeOrd<Concrete> for Elem<Concrete> {
    fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_ord_eq(b),
            _ => None,
        }
    }
    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_neq(b),
            _ => None,
        }
    }
    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_gt(b),
            _ => None,
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_lt(b),
            _ => None,
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_gte(b),
            _ => None,
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_lte(b),
            _ => None,
        }
    }
}

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
                let max = Concrete::max(&self.val).unwrap().into_u256().unwrap();
                if rhs_val > lhs_val.leading_zeros().into() {
                    Some(Elem::Concrete(RangeConcrete {
                        val: max.into(),
                        loc: self.loc,
                    }))
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(
                            (lhs_val << rhs_val).min(max),
                        ),
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
                        I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                    };

                    let min = max * I256::from(-1i32);
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
                            val: Concrete::Int(
                                *lhs_size,
                                as_int.max(min),
                            ),
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
                        val: self
                            .val
                            .u256_as_original(lhs_val >> rhs_val),
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
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
                        let min = max * I256::from(-1i32);


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

pub trait RangeUnary<T, Rhs = Self> {
    /// Perform a logical NOT
    fn range_not(&self) -> Option<Elem<T>>;
    /// Perform a logical AND
    fn range_and(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical OR
    fn range_or(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeUnary<Concrete> for RangeConcrete<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self.val {
            Concrete::Bool(b) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(!b),
                loc: self.loc,
            })),
            _ => None,
        }
    }

    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(*a && *b),
                loc: self.loc,
            })),
            _ => None,
        }
    }

    fn range_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(*a || *b),
                loc: self.loc,
            })),
            _ => None,
        }
    }
}

impl RangeUnary<Concrete> for Elem<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => a.range_not(),
            _ => None,
        }
    }
    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_and(b),
            _ => None,
        }
    }
    fn range_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_or(b),
            _ => None,
        }
    }
}

pub trait RangeCast<T, Rhs = Self> {
    /// Perform a cast on an element to the type of the right hand side
    fn range_cast(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeCast<Concrete> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete {
            val: self.val.clone().cast_from(&other.val)?,
            loc: self.loc,
        }))
    }
}

impl RangeCast<Concrete, Box<RangeDyn<Concrete>>> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Box<RangeDyn<Concrete>>) -> Option<Elem<Concrete>> {
        match (self.val.clone(), other.val.iter().take(1).next()) {
            (
                Concrete::Bytes(_, val),
                Some((
                    _,
                    Elem::Concrete(Self {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            )
            | (Concrete::Bytes(_, val), None) => {
                let mut existing = other.val.clone();
                let new = val
                    .0
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (
                Concrete::DynBytes(val),
                Some((
                    _,
                    Elem::Concrete(Self {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            )
            | (Concrete::DynBytes(val), None) => {
                let mut existing = other.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            e => panic!("here00: {e:?}"),
        }
    }
}

impl RangeCast<Concrete, RangeDyn<Concrete>> for RangeDyn<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        let val: Option<(_, &Elem<Concrete>)> = self.val.iter().take(1).next();
        let o_val: Option<(_, &Elem<Concrete>)> = other.val.iter().take(1).next();
        match (val, o_val) {
            (
                Some((
                    _,
                    &Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    &Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            ) => {
                let mut existing = other.val.clone();
                existing.extend(self.val.clone());
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(..),
                        ..
                    }),
                )),
            ) => {
                let mut existing = other.val.clone();
                existing.extend(self.val.clone());
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(..),
                        ..
                    }),
                )),
            ) => {
                let mut existing = other.val.clone();
                existing.extend(self.val.clone());
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    len: other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (None, None) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            e => panic!("here0: {e:?}"),
        }
    }
}

impl RangeCast<Concrete> for Elem<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_cast(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => a.range_cast(b),
            (Elem::Concrete(a), Elem::ConcreteDyn(b)) => a.range_cast(b),
            e => panic!("here: {e:?}"),
        }
    }
}

pub trait RangeBitwise<T, Rhs = Self> {
    /// Perform a bitwise AND
    fn range_bit_and(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise OR
    fn range_bit_or(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise XOR
    fn range_bit_xor(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeBitwise<Concrete> for RangeConcrete<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a & *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a & *b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }

    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a | *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a | *b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }

    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a ^ *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a ^ *b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }
}

impl RangeBitwise<Concrete> for Elem<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_and(b),
            _ => None,
        }
    }
    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_or(b),
            _ => None,
        }
    }
    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_xor(b),
            _ => None,
        }
    }
}
