use crate::range::Elem;
use ethers_core::types::I256;
use ethers_core::types::U256;
use crate::Concrete;
use crate::range::RangeConcrete;

pub trait RangeAdd<T, Rhs = Self> {
    fn range_add(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeAdd<Concrete> for RangeConcrete<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let size = self.val.int_size().unwrap_or_else(|| other.val.int_size().unwrap_or(256));
                let max = if size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(size)) - 1
                };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(size, lhs_val.saturating_add(rhs_val).min(max)).cast_from(&self.val).expect("bad cast"),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        
                        // neg_v guaranteed to be negative here
                        if neg_v.into_raw() > *val {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(*lhs_size, neg_v.saturating_add(I256::from_raw(*val))),
                                loc: self.loc
                            }))
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: self.val.u256_as_original(val.saturating_sub(neg_v.into_raw())),
                                loc: self.loc
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
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeAdd<Concrete> for Elem<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_add(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(other.clone()),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
    		_ => None
    	}
	}
}

pub trait RangeSub<T, Rhs = Self> {
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
	                    loc: self.loc
	                }))
            	} else {
                    match self.val {
                        Concrete::Int(size, val) => {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(size, val.saturating_sub(I256::from_raw(rhs_val))),
                                loc: self.loc
                            }))
                        }
                        _ => {
                            // TODO: this should cause a revert
                            let val = lhs_val.saturating_sub(rhs_val);
                            Some(Elem::Concrete(RangeConcrete {
                                val: self.val.u256_as_original(val),
                                loc: self.loc
                            }))
                        }
                    }
            	}
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    	let max = if *lhs_size == 256 {
		                    U256::MAX
		                } else {
		                    U256::from(2).pow(U256::from(*lhs_size)) - 1
		                };
                    	Some(Elem::Concrete(RangeConcrete {
                            val: self.val.u256_as_original(val.saturating_add(neg_v.into_raw()).min(max)),
                            loc: self.loc
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
                            val: Concrete::Int(*lhs_size, neg_v.saturating_sub(I256::from_raw(*val).max(min))),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, l.saturating_sub(*r)),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeSub<Concrete> for Elem<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_sub(b),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
    		_ => None
    	}
	}
}



pub trait RangeMul<T, Rhs = Self> {
    fn range_mul(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMul<Concrete> for RangeConcrete<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let size = self.val.int_size().unwrap_or_else(|| other.val.int_size().unwrap_or(256));
                let max = if size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(size)) - 1
                };
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val.saturating_mul(rhs_val).min(max)),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
	                    let min = max * I256::from(-1i32);
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, neg_v.saturating_mul(I256::from_raw(*val)).max(min)),
                            loc: self.loc
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
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeMul<Concrete> for Elem<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_mul(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(other.clone()),
    		_ => None
    	}
	}
}


pub trait RangeExp<T, Rhs = Self> {
    fn range_exp(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeExp<Concrete> for RangeConcrete<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let size = self.val.int_size().unwrap_or_else(|| other.val.int_size().unwrap_or(256));
                let max = if size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(size)) - 1
                };
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val.pow(rhs_val).min(max)),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
                        let min = max * I256::from(-1i32);
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, neg_v.pow(val.as_u32()).max(min)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, l.pow(r.as_u32()).min(max)),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeExp<Concrete> for Elem<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mul(b),
            (Elem::Concrete(a), _) if a.val.into_u256() == Some(U256::zero()) => Some(Elem::from(Concrete::from(U256::from(1)))),
            (_, Elem::Concrete(b)) if b.val.into_u256() == Some(U256::zero()) => Some(other.clone()),
            _ => None
        }
    }
}
pub trait RangeDiv<T, Rhs = Self> {
    fn range_div(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeDiv<Concrete> for RangeConcrete<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val / rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v / I256::from_raw(*val)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *l / *r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeDiv<Concrete> for Elem<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_div(b),
    		_ => None
    	}
	}
}

pub trait RangeMod<T, Rhs = Self> {
    fn range_mod(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMod<Concrete> for RangeConcrete<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val % rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from_raw(*val) %  *neg_v),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v % I256::from_raw(*val)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *l % *r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeMod<Concrete> for Elem<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_mod(b),
    		_ => None
    	}
	}
}

pub trait RangeMin<T, Rhs = Self> {
    fn range_min(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMin<Concrete> for RangeConcrete<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val.min(rhs_val)),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, _), Concrete::Int(_, neg_v)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, _)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *l.min(r)),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeMin<Concrete> for Elem<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_min(b),
    		_ => None
    	}
	}
}


pub trait RangeMax<T, Rhs = Self> {
    fn range_max(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeMax<Concrete> for RangeConcrete<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val.max(rhs_val)),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, _)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*lhs_size, *val),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, _), Concrete::Uint(_, val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Uint(*lhs_size, *val),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *l.max(r)),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeMax<Concrete> for Elem<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_max(b),
    		_ => None
    	}
	}
}

pub trait RangeOrd<T, Rhs = Self> {
	fn range_ord_eq(&self, other: &Rhs) -> Option<Elem<T>>;
	fn range_neq(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_gt(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_lt(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_gte(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_lte(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeOrd<Concrete> for RangeConcrete<Concrete> {
	fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val == rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_, _), Concrete::Int(_, _))
                    | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l == r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val != rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_, _), Concrete::Int(_, _))
                    | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l != r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val > rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l > r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val < rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l < r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val >= rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l >= r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(lhs_val <= rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(l <= r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
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
    fn range_shl(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_shr(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeShift<Concrete> for RangeConcrete<Concrete> {
    fn range_shl(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let size = self.val.int_size().unwrap_or_else(|| other.val.int_size().unwrap_or(256));
                let max = if size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(size)) - 1
                };
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original((lhs_val << rhs_val).min(max)),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
	                    let min = max * I256::from(-1i32);
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, (*neg_v << I256::from_raw(*val)).max(min)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    	let max = if *lhs_size == 256 {
                            I256::MAX
                        } else {
                            I256::from_raw(U256::from(1u8) << U256::from(*lhs_size - 1)) - 1.into()
                        };
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, (*l << *r).min(max)),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }

    fn range_shr(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(Elem::Concrete(RangeConcrete {
                    val: self.val.u256_as_original(lhs_val >> rhs_val),
                    loc: self.loc
                }))
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
						Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from_raw(*val) >> *neg_v),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v >> I256::from_raw(*val)),
                            loc: self.loc
                        }))
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *l >> *r),
                            loc: self.loc
                        }))
                    }
                    _ => None
                }
            }
        }
    }
}

impl RangeShift<Concrete> for Elem<Concrete> {
    fn range_shl(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_shl(b),
    		_ => None
    	}
	}
	fn range_shr(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_shr(b),
    		_ => None
    	}
	}
}

pub trait RangeUnary<T, Rhs = Self> {
    fn range_not(&self) -> Option<Elem<T>>;
    fn range_and(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeUnary<Concrete> for RangeConcrete<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self.val {
            Concrete::Bool(b) => Some(Elem::Concrete(RangeConcrete { val: Concrete::Bool(!b), loc: self.loc })),
            _ => None
        }
    }

    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => {
				Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(*a && *b),
                    loc: self.loc
                }))
            }
            _ => None
        }
    }
}

impl RangeUnary<Concrete> for Elem<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
    	match self {
    		Elem::Concrete(a) => a.range_not(),
    		_ => None
    	}
	}
	fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
    	match (self, other) {
    		(Elem::Concrete(a), Elem::Concrete(b)) => a.range_and(b),
    		_ => None
    	}
	}
}

pub trait RangeCast<T, Rhs = Self> {
    fn range_cast(&self, other: &Rhs) -> Option<Elem<T>>;
}

impl RangeCast<Concrete> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete {
            val: self.val.clone().cast_from(&other.val)?,
            loc: self.loc
        }))
    }
}

impl RangeCast<Concrete> for Elem<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_cast(b),
            _ => None
        }
    }
}