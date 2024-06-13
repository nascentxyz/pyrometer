use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use ethers_core::types::{I256, U256};

impl RangeShift<Concrete> for RangeConcrete<Concrete> {
    fn range_shl(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val > 256.into() {
                    let val = self.val.u256_as_original(U256::zero());
                    let rc = RangeConcrete::new(val, self.loc);
                    return Some(rc.into());
                }

                let max = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .into_u256()
                    .unwrap();
                if self.val.int_val().is_some() {
                    // ints get weird treatment because they can push into the negatives
                    let size = self.val.int_size().unwrap();
                    let op_res = I256::from_raw(lhs_val << rhs_val);
                    let val = Concrete::Int(size, op_res);
                    Some(RangeConcrete::new(val, self.loc).into())
                } else if rhs_val > lhs_val.leading_zeros().into() {
                    Some(RangeConcrete::new(max.into(), self.loc).into())
                } else {
                    let op_res = (lhs_val << rhs_val).min(max);
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::zero() {
                        return Some(Elem::Concrete(self.clone()));
                    }

                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();

                    let (abs, is_min) = neg_v.overflowing_abs();
                    if is_min {
                        if val > &U256::zero() {
                            Some(self.clone().into())
                        } else {
                            let val = Concrete::Int(*lhs_size, I256::zero());
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    } else if val > &U256::from(abs.leading_zeros()) {
                        let val = Concrete::Int(*lhs_size, I256::zero());
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    } else {
                        let raw = I256::from_raw(abs.into_raw() << val);
                        let as_int = if raw == I256::MIN {
                            raw
                        } else {
                            I256::from(-1i32) * raw
                        };

                        let op_res = as_int.max(min);
                        let val = Concrete::Int(*lhs_size, op_res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
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
                    let op_res = self.val.u256_as_original(U256::zero());
                    let rc = RangeConcrete::new(op_res, self.loc);
                    Some(rc.into())
                } else {
                    let op_res = self.val.u256_as_original(lhs_val >> rhs_val);
                    let rc = RangeConcrete::new(op_res, self.loc);
                    Some(rc.into())
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::zero() {
                        Some(Elem::Concrete(self.clone()))
                    } else if val > &U256::from(*lhs_size) {
                        let val = Concrete::Int(*lhs_size, I256::from(-1i32));
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    } else {
                        let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                        let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                        let (abs, is_min) = neg_v.overflowing_abs();
                        let bits = if is_min {
                            255
                        } else {
                            255 - abs.leading_zeros()
                        };

                        if val >= &U256::from(bits) {
                            let val = Concrete::Int(*lhs_size, I256::from(-1i32));
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        } else {
                            let shr_val = abs.into_raw() >> val;
                            let as_int = I256::from_raw(shr_val);
                            let op_res = (I256::from(-1i32) * as_int).max(min);
                            let val = Concrete::Int(*lhs_size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
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

/// Executes the `shift left` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_shl(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_shl(rhs_min),
        lhs_min.range_shl(rhs_max),
        lhs_max.range_shl(rhs_min),
        lhs_max.range_shl(rhs_max),
    ];
    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
    candidates.sort_by(|a, b| match a.range_ord(b, arena) {
        Some(r) => r,
        _ => std::cmp::Ordering::Less,
    });

    if candidates.is_empty() {
        return None;
    }

    if maximize {
        Some(candidates.remove(candidates.len() - 1))
    } else {
        Some(candidates.remove(0))
    }
}

/// Executes the `shift right` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_shr(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_shr(rhs_min),
        lhs_min.range_shr(rhs_max),
        lhs_max.range_shr(rhs_min),
        lhs_max.range_shr(rhs_max),
    ];
    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
    candidates.sort_by(|a, b| match a.range_ord(b, arena) {
        Some(r) => r,
        _ => std::cmp::Ordering::Less,
    });

    if candidates.is_empty() {
        return None;
    }

    if maximize {
        Some(candidates.remove(candidates.len() - 1))
    } else {
        Some(candidates.remove(0))
    }
}
