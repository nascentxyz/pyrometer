use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

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
            _ => match (&self.val, &other.val.into_u256()) {
                // exponent must be positive otherwise return None.
                (Concrete::Int(lhs_size, neg_v), Some(val)) => {
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
///
/// TODO: Add wrapping/unchecked version
pub fn exec_exp(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    _unchecked: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    // TODO: Improve this
    let candidates = vec![
        lhs_min.range_exp(rhs_min),
        lhs_min.range_exp(rhs_max),
        lhs_max.range_exp(rhs_min),
        lhs_max.range_exp(rhs_max),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DummyGraph;
    use ethers_core::types::{I256, U256};
    use solang_parser::pt::Loc;

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(759375)));
    }

    #[test]
    fn saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX));
    }

    #[test]
    fn sized_saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn int_uint() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-1i32)));
    }

    #[test]
    fn int_uint_2() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(15i32)), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(
            result.val,
            Concrete::Int(256, I256::from(-437893890380859375i128))
        );
    }

    #[test]
    fn saturating_int_int() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::MIN + I256::from(1i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(2i32)), Loc::Implicit);
        let result = x.range_exp(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn sized_saturating_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-2i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn exec_sized_uint_uint_saturating() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(2).into();
        let lhs_max = rc_uint_sized(150).into();
        let rhs_min = rc_uint_sized(3).into();
        let rhs_max = rc_uint_sized(200).into();

        let max_result = exec_exp(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_exp(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(8)));
    }
}
