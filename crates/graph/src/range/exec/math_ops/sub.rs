use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;

impl RangeSub<Concrete> for RangeConcrete<Concrete> {
    fn range_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let op_res = lhs_val.saturating_sub(rhs_val);
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    match self.val {
                        Concrete::Int(size, val) => {
                            let min_int =
                                Concrete::min_of_type(&self.val).unwrap().int_val().unwrap();
                            let op_res = val.saturating_sub(I256::from_raw(rhs_val)).max(min_int);
                            let val = Concrete::Int(size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                        _ => {
                            // TODO: this should cause a revert
                            let op_res = lhs_val.saturating_sub(rhs_val);
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let tmp = Concrete::Uint(*lhs_size, U256::zero());
                    let max = Concrete::max_of_type(&tmp).unwrap().uint_val().unwrap();
                    let abs = neg_v.unsigned_abs();
                    let op_res = val.saturating_add(abs).min(max);
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = neg_v.saturating_sub(I256::from_raw(*val).max(min));
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = l.saturating_sub(*r).max(min).min(max);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_sub(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if lhs_val > rhs_val {
                    let op_res = lhs_val.overflowing_sub(rhs_val).0;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    match self.val {
                        Concrete::Int(size, val) => {
                            let op_res = val.overflowing_sub(I256::from_raw(rhs_val)).0;
                            let val = Concrete::Int(size, op_res).size_wrap();
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                        _ => {
                            let op_res = lhs_val.overflowing_sub(rhs_val).0;
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                }
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let op_res = val.overflowing_add(neg_v.into_raw()).0;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let op_res = I256::from_raw(neg_v.into_raw().overflowing_sub(*val).0);
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete::new(
                        Concrete::Int(*lhs_size, l.overflowing_sub(*r).0).size_wrap(),
                        self.loc,
                    )))
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

/// Executes an subtraction given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound of the operation.
///
/// ### Explanation
/// A fact about subtraction is that the largest value possible (in unbounded integer space), is between the left hand side _maximum_ and right hand side _minimum_ and the smallest
/// is between the left hand side _minimum_ and right hand side _maximum_ values. This fact is used in normal "unbounded" (really, saturating) subtraction calculations as well as wrapping subtraction as basis for another fact:
///
/// In wrapping subtraction, if the bounds allow for optionally wrapping (e.g.: maximum - minimum does not wrap, but minimum - maximum does wrap), we can
/// by extension include *both* the type's maximum and minimum.
///
/// For example, assume:<code>
///uint256 x: [101, 2<sup>256</sup>-1]
///uint256 y: [100, 2<sup>256</sup>-1]
///unchecked { x - y }
///</code>
///
/// In this subtraction of `x - y`, `101 - 100` does not wrap, but `101 - 102` does (unsigned integer). We can construct a value of x and y such that
/// the result of `x - y` is equal to <code>2<sup>256</sup>-1</code> (`101 - 102`) or `0` (`101 - 101`). Therefore, the new bounds
/// on `unchecked { x - y }` is <code>[0, 2<sup>256</sup>-1]</code>.
///
/// ### Note
/// Signed integers use 2's complement representation so the maximum is <code>2<sup>size - 1</sup> - 1</code>, while unsigned integers are <code>2<sup>size</sup> - 1</code>
///
///
/// ### Truth Tables
/// Truth table for `checked sub` operation:
///
///| Sub             | Uint                                                                                         | Int                                                                                          | BytesX | Address | Bytes | String |
///|-----------------|----------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------|--------|---------|-------|--------|
///| **Uint**        | _min_: lhs<sub>min</sub> - rhs<sub>max</sub><br>_max_: lhs<sub>max</sub> - rhs<sub>min</sub> | _min_: lhs<sub>min</sub> - rhs<sub>max</sub><br>_max_: lhs<sub>max</sub> - rhs<sub>min</sub> | N/A    | N/A     | N/A   | N/A    |
///| **Int**         | _min_: lhs<sub>min</sub> - rhs<sub>max</sub><br>_max_: lhs<sub>max</sub> - rhs<sub>min</sub> | _min_: lhs<sub>min</sub> - rhs<sub>max</sub><br>_max_: lhs<sub>max</sub> - rhs<sub>min</sub> | N/A    | N/A     | N/A   | N/A    |
///| **BytesX**      | N/A                                                                                          | N/A                                                                                          | N/A    | N/A     | N/A   | N/A    |
///| **Address**     | N/A                                                                                          | N/A                                                                                          | N/A    | N/A     | N/A   | N/A    |
///| **Bytes**       | N/A                                                                                          | N/A                                                                                          | N/A    | N/A     | N/A   | N/A    |
///| **String**      | N/A                                                                                          | N/A                                                                                          | N/A    | N/A     | N/A   | N/A    |
///
/// Truth table for `wrapping sub` operation:
///
///| Wrapping Sub              | Uint                                                                                                                                          | Int                                                                                                                                           | BytesX | Address | Bytes | String |
///|---------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------------------------------|--------|---------|-------|--------|
///| **Uint**                  | _min_: {0, lhs<sub>min</sub> - rhs<sub>max</sub>}<br>_max_: {2<sup>size</sup> - 1, lhs<sub>max</sub> - rhs<sub>min</sub>}                     | _min_: {0, lhs<sub>min</sub> - rhs<sub>max</sub>}<br>_max_: {2<sup>size</sup> - 1, lhs<sub>max</sub> - rhs<sub>min</sub>}                     | N/A    | N/A     | N/A   | N/A    |
///| **Int**                   | _min_: {-2<sup>size-1</sup>, lhs<sub>min</sub> - rhs<sub>max</sub>}<br>_max_: {2<sup>size-1</sup> - 1, lhs<sub>max</sub> - rhs<sub>min</sub>} | _min_: {-2<sup>size-1</sup>, lhs<sub>min</sub> - rhs<sub>max</sub>}<br>_max_: {2<sup>size-1</sup> - 1, lhs<sub>max</sub> - rhs<sub>min</sub>} | N/A    | N/A     | N/A   | N/A    |
///| **BytesX**                | N/A                                                                                                                                           | N/A                                                                                                                                           | N/A    | N/A     | N/A   | N/A    |
///| **Address**               | N/A                                                                                                                                           | N/A                                                                                                                                           | N/A    | N/A     | N/A   | N/A    |
///| **Bytes**                 | N/A                                                                                                                                           | N/A                                                                                                                                           | N/A    | N/A     | N/A   | N/A    |
///| **String**                | N/A                                                                                                                                           | N/A                                                                                                                                           | N/A    | N/A     | N/A   | N/A    |
pub fn exec_sub(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    wrapping: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    // quick check if rhs is const and zero, if so return min or max
    if wrapping {
        let mut candidates = vec![];
        let mut all_overflowed = true;
        let mut one_overflowed = false;
        let zero = Elem::Concrete(RangeConcrete::new(
            Concrete::from(U256::zero()),
            Loc::Implicit,
        ));
        let add_candidate = |lhs: &Elem<Concrete>,
                             rhs: &Elem<Concrete>,
                             candidates: &mut Vec<Elem<Concrete>>,
                             all_overflowed: &mut bool,
                             one_overflowed: &mut bool,
                             arena: &mut RangeArena<Elem<Concrete>>| {
            if let Some(c) = lhs.range_wrapping_sub(rhs) {
                let lhs_neg = matches!(lhs.range_ord(&zero, arena), Some(std::cmp::Ordering::Less));
                let rhs_neg = matches!(rhs.range_ord(&zero, arena), Some(std::cmp::Ordering::Less));
                let signed = lhs_neg || rhs_neg;

                let overflowed = if signed {
                    // signed safemath: (rhs >= 0 && c <= lhs) || (rhs < 0 && c > lhs) ==>  no overflowed --invert-> overflowed
                    // ( rhs < 0 ∣∣ c > lhs) && ( rhs ≥ 0 ∣∣ c ≤ lhs)

                    (rhs_neg
                        || matches!(c.range_ord(lhs, arena), Some(std::cmp::Ordering::Greater)))
                        && (!rhs_neg
                            || matches!(
                                c.range_ord(lhs, arena),
                                Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                            ))
                } else {
                    // unsigned safemath: c < a ==> overflowed
                    matches!(c.range_ord(lhs, arena), Some(std::cmp::Ordering::Greater))
                };

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

        // If we have a conditional overflow, add the min and max of the type of lhs to the candidates
        if !all_overflowed && one_overflowed {
            let add_extremes = |elem: &Elem<Concrete>, candidates: &mut Vec<Elem<_>>| {
                if let Some(c) = elem.maybe_concrete() {
                    if let Some(max) = Concrete::max_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(max, c.loc).into());
                    }

                    if let Some(min) = Concrete::min_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(min, c.loc).into());
                    }
                }
            };

            add_extremes(lhs_min, &mut candidates);
            add_extremes(lhs_max, &mut candidates);
        }

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
    } else if maximize {
        // if we are maximizing, the largest value will always just be the the largest value - the smallest value
        lhs_max.range_sub(rhs_min)
    } else {
        // if we are minimizing, the smallest value will always be smallest value - largest value
        lhs_min.range_sub(rhs_max)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DummyGraph;
    use ethers_core::types::U256;
    use solang_parser::pt::Loc;

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(10)));
    }

    #[test]
    fn saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::zero()));
    }

    #[test]
    fn sized_saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::zero()));
    }

    #[test]
    fn int_big_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(16)));
    }

    #[test]
    fn big_int_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(16)));
    }

    #[test]
    fn int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(0i32)));
    }

    #[test]
    fn max_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn int_max_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::MAX), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MIN));
    }

    #[test]
    fn saturating_int_int() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::MIN + I256::from(1i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(2i32)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MIN));
    }

    #[test]
    fn sized_saturating_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(2i32)), Loc::Implicit);
        let result = x.range_sub(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::zero()), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let result = x
            .range_wrapping_sub(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX));
    }

    #[test]
    fn sized_wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::zero()), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(1)), Loc::Implicit);
        let result = x
            .range_wrapping_sub(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(15i32)), Loc::Implicit);
        let result = x
            .range_wrapping_sub(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-16i32)));
    }

    #[test]
    fn wrapping_int_int_2() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_sub(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn sized_wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-128i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_sub(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(127i32)));
    }

    #[test]
    fn exec_sized_uint_uint_saturating() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(105).into();
        let lhs_max = rc_uint_sized(150).into();
        let rhs_min = rc_uint_sized(10).into();
        let rhs_max = rc_uint_sized(200).into();

        let max_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(140)));
        let min_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(0)));
    }

    #[test]
    fn exec_sized_wrapping_uint_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(105).into();
        let lhs_max = rc_uint_sized(150).into();
        let rhs_min = rc_uint_sized(10).into();
        let rhs_max = rc_uint_sized(200).into();

        let max_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(0)));
    }

    #[test]
    fn exec_sized_wrapping_int_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(127).into();
        let rhs_min = rc_uint_sized(0).into();
        let rhs_max = rc_uint_sized(255).into();

        let max_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn exec_sized_wrapping_int_int_max() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(-100).into();
        let rhs_min = rc_int_sized(-5).into();
        let rhs_max = rc_int_sized(5).into();

        let max_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_sub(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-128i32)));
    }
}
