use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

use ethers_core::types::{I256, U256};

impl RangeDiv<Concrete> for RangeConcrete<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == 0.into() {
                    None
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(lhs_val / rhs_val),
                        loc: self.loc,
                    }))
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    if neg_v == &I256::from(0) {
                        None
                    } else {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(
                                *lhs_size,
                                I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32),
                            ),
                            loc: self.loc,
                        }))
                    }
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::from(0) {
                        None
                    } else {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v / I256::from_raw(*val)),
                            loc: self.loc,
                        }))
                    }
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::from(0) {
                        None
                    } else {
                        let (val, overflow) = l.overflowing_div(*r);
                        if overflow {
                            None
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(*lhs_size, val),
                                loc: self.loc,
                            }))
                        }
                    }
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == 0.into() {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(U256::zero()),
                        loc: self.loc,
                    }))
                } else {
                    Some(Elem::Concrete(RangeConcrete {
                        val: self.val.u256_as_original(lhs_val / rhs_val),
                        loc: self.loc,
                    }))
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    if neg_v == &I256::from(0) {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from(0i32)),
                            loc: self.loc,
                        }))
                    } else {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(
                                *lhs_size,
                                I256::from_raw(val / neg_v.into_raw()) * I256::from(-1i32),
                            ),
                            loc: self.loc,
                        }))
                    }
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::from(0) {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from(0i32)),
                            loc: self.loc,
                        }))
                    } else {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, *neg_v / I256::from_raw(*val)),
                            loc: self.loc,
                        }))
                    }
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::from(0) {
                        Some(Elem::Concrete(RangeConcrete {
                            val: Concrete::Int(*lhs_size, I256::from(0i32)),
                            loc: self.loc,
                        }))
                    } else {
                        let (val, overflow) = l.overflowing_div(*r);
                        if overflow {
                            None
                        } else {
                            Some(Elem::Concrete(RangeConcrete {
                                val: Concrete::Int(*lhs_size, val),
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

impl RangeDiv<Concrete> for Elem<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_div(b),
            _ => None,
        }
    }

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_div(b),
            _ => None,
        }
    }
}