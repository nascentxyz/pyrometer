use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use alloy_primitives::{I256, U256};
use solang_parser::pt::Loc;

impl RangeDiv<Concrete> for RangeConcrete<Concrete> {
    fn range_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == U256::ZERO {
                    None
                } else {
                    let op_res = lhs_val / rhs_val;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    // Divisor cannot be zero because it would have been converted
                    // to a uint
                    let abs = neg_v.into_sign_and_abs().1;
                    let op_res = I256::from_raw(val / abs).saturating_div(I256::MINUS_ONE);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    if val == &U256::ZERO {
                        None
                    } else {
                        let abs = neg_v.into_sign_and_abs().1;
                        let op_res = I256::from_raw(abs / *val).saturating_div(I256::MINUS_ONE);
                        let val = Concrete::Int(*lhs_size, op_res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    if r == &I256::ZERO {
                        None
                    } else {
                        let (op_res, overflow) = l.overflowing_div(*r);
                        if overflow {
                            let max = Concrete::max_of_type(&self.val).unwrap().int_val().unwrap();
                            let val = Concrete::Int(*lhs_size, max);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        } else {
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

    fn range_wrapping_div(&self, other: &Self) -> Option<Elem<Concrete>> {
        // Only negative Int / negative Int needs overflowing_div
        match (&self.val, &other.val) {
            (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r))
                if *l < I256::ZERO && *r < I256::ZERO =>
            {
                let op_res = l.overflowing_div(*r).0;
                let val = Concrete::Int(*lhs_size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => self.range_div(other),
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

/// Executes an division given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
///
/// ### Note
/// Signed integers use 2's complement representation so the maximum is <code>2<sup>size - 1</sup> - 1</code>, while unsigned integers are <code>2<sup>size</sup> - 1</code>
///
///
/// ### Truth Tables
/// Truth table for `checked div` operation:
///
/// `todo!()`
///
/// Truth table for `wrapping div` operation:
///
/// `todo!()`
///
pub fn exec_div(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    wrapping: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let mut candidates = vec![];
    let saturating_div = |lhs: &Elem<_>, rhs: &Elem<_>, candidates: &mut Vec<Elem<Concrete>>| {
        if let Some(c) = lhs.range_div(rhs) {
            candidates.push(c);
        }
    };

    let one = Elem::from(Concrete::from(U256::from(1)));
    let negative_one = Elem::from(Concrete::from(I256::MINUS_ONE));

    let min_contains = matches!(
        rhs_min.range_ord(&one, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&one, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    // for division, if 1 is contained by the denominator, we can just add the left hand side as candidates
    if min_contains && max_contains {
        candidates.push(lhs_min.clone());
        candidates.push(lhs_max.clone());
    }

    let min_contains_neg_one = matches!(
        rhs_min.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains_neg_one = matches!(
        rhs_max.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains_neg_one && max_contains_neg_one {
        // if the divisor contains -1, we can just saturating multiply by -1
        if matches!(
            lhs_min.range_ord(&negative_one, arena),
            Some(std::cmp::Ordering::Less)
        ) {
            // lhs can be negative, check if it contains int_min
            let type_min = Concrete::min_of_type(&lhs_min.maybe_concrete().unwrap().val).unwrap();
            let int_val = type_min.int_val().unwrap();
            let min = Elem::from(type_min);
            let min_plus_one = Elem::Concrete(rc_i256_sized(int_val + I256::ONE));

            let lhs_contains_int_min = matches!(
                lhs_min.range_ord(&min, arena),
                Some(std::cmp::Ordering::Equal)
            );

            let max_contains_int_min_plus_one = matches!(
                rhs_max.range_ord(&min_plus_one, arena),
                Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
            );

            // add int max to candidates
            if lhs_contains_int_min && max_contains_int_min_plus_one {
                if let Some(c) = min_plus_one.range_mul(&negative_one) {
                    candidates.push(c);
                }
            } else if let Some(c) = lhs_min.range_mul(&negative_one) {
                // add min * -1
                candidates.push(c);
            }
        } else if let Some(c) = lhs_min.range_mul(&negative_one) {
            // add min * -1
            candidates.push(c);
        }

        if let Some(c) = lhs_max.range_mul(&negative_one) {
            candidates.push(c);
        }
    }

    if wrapping {
        let mut all_overflowed = true;
        let mut one_overflowed = false;
        let add_candidate = |lhs: &Elem<Concrete>,
                             rhs: &Elem<Concrete>,
                             candidates: &mut Vec<Elem<Concrete>>,
                             all_overflowed: &mut bool,
                             one_overflowed: &mut bool,
                             arena: &mut RangeArena<Elem<Concrete>>| {
            if let Some(c) = lhs.range_wrapping_div(rhs) {
                let mut overflowed = false;
                let neg_one =
                    RangeConcrete::new(Concrete::Int(8, I256::MINUS_ONE), Loc::Implicit).into();
                if matches!(
                    lhs.range_ord(&neg_one, arena),
                    Some(std::cmp::Ordering::Less)
                ) {
                    // rhs == -1
                    let div_neg_one = matches!(
                        rhs.range_ord(&neg_one, arena),
                        Some(std::cmp::Ordering::Equal)
                    );

                    let type_min =
                        Concrete::min_of_type(&lhs.maybe_concrete().unwrap().val).unwrap();
                    let min = RangeConcrete::new(type_min, Loc::Implicit).into();

                    // lhs == INT_MIN
                    let num_int_min =
                        matches!(lhs.range_ord(&min, arena), Some(std::cmp::Ordering::Equal));
                    if div_neg_one && num_int_min {
                        overflowed = true;
                    }
                }

                if *all_overflowed && !overflowed {
                    *all_overflowed = false;
                }

                if !*one_overflowed && overflowed {
                    *one_overflowed = true;
                }

                candidates.push(c);
            }
        };

        add_candidate(
            lhs_min,
            rhs_min,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
            arena,
        );
        add_candidate(
            lhs_min,
            rhs_max,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
            arena,
        );
        add_candidate(
            lhs_max,
            rhs_min,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
            arena,
        );
        add_candidate(
            lhs_max,
            rhs_max,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
            arena,
        );

        if one_overflowed {
            let add_min = |elem: &Elem<Concrete>, candidates: &mut Vec<Elem<_>>| {
                if let Some(c) = elem.maybe_concrete() {
                    if let Some(min) = Concrete::min_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(min, c.loc).into());
                    }
                }
            };
            add_min(lhs_min, &mut candidates);
            add_min(lhs_max, &mut candidates);
        }
    } else {
        // without inspecting types of lhs and rhs, its easiest just to run them all and
        // sort
        saturating_div(lhs_min, rhs_min, &mut candidates);
        saturating_div(lhs_min, rhs_max, &mut candidates);
        saturating_div(lhs_max, rhs_min, &mut candidates);
        saturating_div(lhs_max, rhs_max, &mut candidates);
    }

    // Sort the candidates
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

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(3)));
    }

    #[test]
    fn uint_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(5i32)),
            Loc::Implicit,
        );
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(3)));
    }

    #[test]
    fn uint_neg_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(-5i32)),
            Loc::Implicit,
        );
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::unchecked_from(-3i32)));
    }

    #[test]
    fn neg_int_uint() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(-15i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::unchecked_from(-3i32)));
    }

    #[test]
    fn neg_int_neg_int() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(-15i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(-5i32)),
            Loc::Implicit,
        );
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::unchecked_from(3i32)));
    }

    #[test]
    fn uint_zero() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::ZERO), Loc::Implicit);
        assert!(x.range_div(&y).is_none());
    }

    #[test]
    fn int_zero() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::unchecked_from(-15i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Uint(256, U256::ZERO), Loc::Implicit);
        assert!(x.range_div(&y).is_none());
    }

    #[test]
    fn wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::MINUS_ONE), Loc::Implicit);
        let result = x.range_wrapping_div(&y).unwrap();
        let expected = x.clone();
        assert_eq!(result, expected.into());
    }

    #[test]
    fn nonwrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::MINUS_ONE), Loc::Implicit);
        let result = x.range_div(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn exec_sized_uint_uint_saturating() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(5).into();
        let lhs_max = rc_uint_sized(15).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(20).into();

        let max_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(15)));
        let min_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::ZERO));
    }

    #[test]
    fn exec_sized_wrapping_uint_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(5).into();
        let lhs_max = rc_uint_sized(15).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(16).into();

        let max_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(15)));
        let min_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::ZERO));
    }

    #[test]
    fn exec_sized_wrapping_int_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(127).into();
        let rhs_min = rc_uint_sized(0).into();
        let rhs_max = rc_uint_sized(255).into();

        let max_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(
            max_result.val,
            Concrete::Int(8, I256::unchecked_from(127i32))
        );
        let min_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(
            min_result.val,
            Concrete::Int(8, I256::unchecked_from(-128i32))
        );
    }

    #[test]
    fn exec_sized_wrapping_int_int_max() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(-100).into();
        let rhs_min = rc_int_sized(-5).into();
        let rhs_max = rc_int_sized(5).into();

        let max_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(
            max_result.val,
            Concrete::Int(8, I256::unchecked_from(127i32))
        );
        let min_result = exec_div(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(
            min_result.val,
            Concrete::Int(8, I256::unchecked_from(-128i32))
        );
    }
}
