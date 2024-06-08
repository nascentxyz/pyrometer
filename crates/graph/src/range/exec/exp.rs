use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use ethers_core::types::U256;

impl RangeExp<Concrete> for RangeConcrete<Concrete> {
    fn range_exp(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max_of_type(&self.val).unwrap();

                let op_res = lhs_val.checked_pow(rhs_val);
                let op_res = if let Some(num) = op_res {
                    num.min(max.into_u256().unwrap())
                } else {
                    max.into_u256().unwrap()
                };

                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let pow2 = val % U256::from(2) == 0.into();
                    let val = if val > &U256::from(u32::MAX) {
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
                    let rc = RangeConcrete::new(val, self.loc);
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

/// Executes the `exponentiation` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_exp(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    // TODO: Improve this
    let candidates = vec![
        lhs_min.range_exp(&rhs_min),
        lhs_min.range_exp(&rhs_max),
        lhs_max.range_exp(&rhs_min),
        lhs_max.range_exp(&rhs_max),
    ];
    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
    candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
