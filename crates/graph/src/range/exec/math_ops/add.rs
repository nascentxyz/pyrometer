use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use ethers_core::types::I256;

impl RangeAdd<Concrete> for RangeConcrete<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                // `max_of_type` cannot fail on uint
                let max_uint = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .into_u256()
                    .unwrap();
                // min { a + b, max } to cap at maximum of lhs sizing
                let op_res = lhs_val.saturating_add(rhs_val).min(max_uint);
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => {
                match (&self.val, &other.val) {
                    (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                    | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                        // neg_v guaranteed to be negative here
                        let abs = neg_v.unsigned_abs();
                        if abs > *val {
                            // |b| - a
                            let op_res =
                                I256::from_raw(abs.saturating_sub(*val)) * I256::from(-1i32);
                            let val = Concrete::Int(*lhs_size, op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        } else {
                            // a - |b|
                            let op_res = val.saturating_sub(abs);
                            let val = self.val.u256_as_original(op_res);
                            let rc = RangeConcrete::new(val, self.loc);
                            Some(rc.into())
                        }
                    }
                    (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                        // `min_of_type` cannot fail on int
                        let min = Concrete::min_of_type(&self.val).unwrap().int_val().unwrap();
                        // lhs + rhs when both are negative is effectively lhs - rhs which means
                        // we saturate at the minimum value of the left hand side.
                        // therefore, max{ l + r, min } is the result
                        let op_res = l.saturating_add(*r).max(min);
                        let val = Concrete::Int(*lhs_size, op_res);
                        let rc = RangeConcrete::new(val, self.loc);
                        Some(rc.into())
                    }
                    _ => None,
                }
            }
        }
    }

    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.overflowing_add(rhs_val).0;
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(..), Concrete::Int(..))
                | (Concrete::Int(..), Concrete::Uint(..)) => {
                    // just fall back to normal implementation because
                    // a positive and negative cannot overflow in addition
                    self.range_add(other)
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let op_res = l.overflowing_add(*r).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeAdd<Concrete> for Elem<Concrete> {
    fn range_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(other.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_add(b),
            _ => None,
        }
    }
    fn range_wrapping_add(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(other.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(self.clone()),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_add(b),
            _ => None,
        }
    }
}

/// Executes an addition given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound of the operation.
///
/// ### Explanation
/// A fact about addition is that the smallest value possible (in unbounded integer space), is between two _minimum_ values and the largest
/// is between two _maximum_ values. This fact is used in normal "unbounded" (really, saturating) addition calculations as well as wrapping addition as basis for another fact:
///
/// In wrapping addition, if the bounds allow for optionally wrapping (e.g.: minimum + minimum does not wrap, but maximum + maximum does wrap), we can
/// by extension include *both* the type's maximum and minimum.
///
/// For example, assume:<code>
///uint256 x: [100, 2<sup>256</sup>-1]
///uint256 y: [100, 2<sup>256</sup>-1]
///unchecked { x + y }
///</code>
///
/// In this addition of `x+y`, `100+100` does not wrap, but <code>2<sup>256</sup>-1 + 2<sup>256</sup>-1</code> does. We can construct a value of x and y such that
/// the result of `x+y` is equal to <code>2<sup>256</sup>-1</code> (<code>100 + 2<sup>256</sup>-101</code>) or `0` (<code>100 + 2<sup>256</sup>-99</code>). Therefore, the new bounds
/// on `unchecked { x + y }` is <code>[0, 2<sup>256</sup>-1]</code>.
///
///
/// ### Note
/// Signed integers use 2's complement representation so the maximum is <code>2<sup>size - 1</sup> - 1</code>, while unsigned integers are <code>2<sup>size</sup> - 1</code>
///
///
/// ### Truth Tables
/// Truth table for `checked add` operation:
///
///| Add             | Uint                                                                                     | Int                                                                                      | BytesX | Address | Bytes | String |
///|-----------------|------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|--------|---------|-------|--------|
///| **Uint**        | min: lhs<sub>min</sub> + rhs<sub>min</sub><br>max: lhs<sub>max</sub> + rhs<sub>max</sub> | min: lhs<sub>min</sub> + rhs<sub>min</sub><br>max: lhs<sub>max</sub> + rhs<sub>max</sub> | N/A    | N/A     | N/A   | N/A    |
///| **Int**         | min: lhs<sub>min</sub> + rhs<sub>min</sub><br>max: lhs<sub>max</sub> + rhs<sub>max</sub> | min: lhs<sub>min</sub> + rhs<sub>min</sub><br>max: lhs<sub>max</sub> + rhs<sub>max</sub> | N/A    | N/A     | N/A   | N/A    |
///| **BytesX**      | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **Address**     | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **Bytes**       | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **String**      | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///
/// Truth table for `wrapping add` operation:
///
///| Wrapping Add              | Uint                                                                                                                                    | Int                                                                                                                   | BytesX | Address | Bytes | String |
///|---------------------------|-----------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------|--------|---------|-------|--------|
///| **Uint**                  | min: {0, lhs<sub>min</sub> + rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>}                   | min: {0, lhs<sub>min</sub> + rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>} | N/A    | N/A     | N/A   | N/A    |
///| **Int**                   | min: {-2<sup>size-1</sup>, lhs<sub>min</sub> + rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>} | min: {0, lhs<sub>min</sub> + rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>} | N/A    | N/A     | N/A   | N/A    |
///| **BytesX**                | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
///| **Address**               | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
///| **Bytes**                 | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
///| **String**                | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
pub fn exec_add(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    wrapping: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    if wrapping {
        let mut candidates = vec![];
        let mut all_overflowed = true;
        let mut one_overflowed = false;
        let add_candidate = |lhs: &Elem<Concrete>,
                             rhs: &Elem<Concrete>,
                             candidates: &mut Vec<Elem<Concrete>>,
                             all_overflowed: &mut bool,
                             one_overflowed: &mut bool,
                             arena: &mut RangeArena<Elem<Concrete>>| {
            if let Some(c) = lhs.range_wrapping_add(rhs) {
                let overflowed = matches!(c.range_ord(lhs, arena), Some(std::cmp::Ordering::Less));

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

        // We need to check if there is a value in [lhs_min, lhs_max] that when added to a value in [rhs_min, rhs_max]
        // will not overflow
        //
        // If that is the case we can additionally compare saturating addition cases to the candidates
        if !all_overflowed {
            // We didnt overflow in some case, add saturating addition candidates
            let saturating_add =
                |lhs: &Elem<_>, rhs: &Elem<_>, candidates: &mut Vec<Elem<Concrete>>| -> bool {
                    if let Some(c) = lhs.range_add(rhs) {
                        candidates.push(c);
                        true
                    } else {
                        false
                    }
                };
            // if max + max returned a result, that saturating addition will be largest possible candidate
            if !saturating_add(lhs_max, rhs_max, &mut candidates) {
                saturating_add(lhs_min, rhs_min, &mut candidates);
                saturating_add(lhs_min, rhs_max, &mut candidates);
                saturating_add(lhs_max, rhs_min, &mut candidates);
            }
        }

        // We need to check if there is a value in [lhs_min, lhs_max] that when added to a value in [rhs_min, rhs_max]
        // will overflow and can result in the minimum value of the type
        //
        // We can do this by checking if we can conditionally overflow.
        let conditional_overflow = !all_overflowed && one_overflowed;
        if conditional_overflow {
            let add_min = |elem: &Elem<Concrete>, candidates: &mut Vec<Elem<_>>| {
                if let Some(c) = elem.maybe_concrete() {
                    if let Some(min) = Concrete::min_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(min, c.loc).into());
                    }

                    if let Some(max) = Concrete::max_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(max, c.loc).into());
                    }
                }
            };
            // We are able to conditionally overflow, so add min
            add_min(lhs_min, &mut candidates);
            add_min(lhs_max, &mut candidates);
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
    } else if maximize {
        // if we are maximizing, the largest value will always just be the the largest value + the largest value
        lhs_max.range_add(rhs_max)
    } else {
        // if we are minimizing, the smallest value will always just be the the smallest value + the smallest value
        lhs_min.range_add(rhs_min)
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
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(20)));
    }

    #[test]
    fn saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX));
    }

    #[test]
    fn sized_saturating_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(254)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn int_big_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(14)));
    }

    #[test]
    fn big_int_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-14i32)));
    }

    #[test]
    fn int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-30i32)));
    }

    #[test]
    fn saturating_int_int() {
        let x = RangeConcrete::new(
            Concrete::Int(256, I256::MIN + I256::from(1i32)),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-2i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MIN));
    }

    #[test]
    fn sized_saturating_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-2i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::MAX), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(2)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(1)));
    }

    #[test]
    fn sized_wrapping_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(8, U256::from(255)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(2)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(1)));
    }

    #[test]
    fn wrapping_big_int_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_add(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-14i32)));
    }

    #[test]
    fn wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::MAX));
    }

    #[test]
    fn sized_wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-128i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-1i32)), Loc::Implicit);
        let result = x
            .range_wrapping_add(&y)
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

        let max_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(115)));
    }

    #[test]
    fn exec_sized_wrapping_uint_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(105).into();
        let lhs_max = rc_uint_sized(150).into();
        let rhs_min = rc_uint_sized(10).into();
        let rhs_max = rc_uint_sized(200).into();

        let max_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_add(
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

        let max_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_add(
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

        let max_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_add(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-128i32)));
    }
}
