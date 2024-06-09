use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use ethers_core::types::{I256, U256};

impl RangeMul<Concrete> for RangeConcrete<Concrete> {
    fn range_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let max = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .into_u256()
                    .unwrap();
                let mut op_res = lhs_val.saturating_mul(rhs_val).min(max);
                if let Some(min) = Concrete::min_of_type(&self.val).unwrap().into_u256() {
                    op_res = op_res.max(min);
                }
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = neg_v.saturating_mul(I256::from_raw(*val)).max(min).min(max);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let tmp = Concrete::Int(*lhs_size, I256::from(0i32));
                    let min = Concrete::min_of_type(&tmp).unwrap().int_val().unwrap();
                    let max = Concrete::max_of_type(&tmp).unwrap().int_val().unwrap();

                    let op_res = l.saturating_mul(*r).min(max).max(min);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.overflowing_mul(rhs_val).0;
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) => {
                    let op_res = neg_v.overflowing_mul(I256::from_raw(*val)).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let op_res = l.overflowing_mul(*r).0;
                    let val = Concrete::Int(*lhs_size, op_res).size_wrap();
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
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
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(other.clone()),
            (Elem::Concrete(a), b) if a.val.is_one() => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.is_one() => Some(a.clone()),
            _ => None,
        }
    }

    fn range_wrapping_mul(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_wrapping_mul(b),
            (Elem::Concrete(a), _) if a.val.is_zero() => Some(self.clone()),
            (_, Elem::Concrete(b)) if b.val.is_zero() => Some(other.clone()),
            (Elem::Concrete(a), b) if a.val.is_one() => Some(b.clone()),
            (a, Elem::Concrete(b)) if b.val.is_one() => Some(a.clone()),
            _ => None,
        }
    }
}

/// Executes an multiplication given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
///
/// ### Explanation
/// A fact about multiplication is that the smallest value possible (in unbounded unsigned integer space), is between two _minimum_
/// values and the largest is between two _maximum_ values. In the unbounded signed integer space, the smallest value will be
/// the product of the most negative value and most positive value.
///
/// Pyrometer _overestimates_ products of multiplication in both the saturating and wrapping cases. This is due to
/// to the fact that the multiplicants may not contain factors of the maximum/minimum. That is to say,
/// the factors of, for example, <code>2<sup>size</sup>-1</code> may not exactly be in the left hand side
/// and right hand side. By default, we allow this overestimation. The only case we cover is when both elements' minimums
/// product always overflows.
///
///
/// For example, assume:<code>
///uint256 x: [2<sup>240</sup>, 2<sup>256</sup>-1]
///uint256 y: [2<sup>16</sup>, 2<sup>256</sup>-1]
///unchecked { x * y }
///</code>
///
/// In this multiplication of `x*y`, it will always overflow so the minimum is still `x.min * y.min`, and the maximum is still `x.max * y.max`. However,
/// had `x.min * y.min` _not_ overflowed, the maximum would have been `type(uint256).max` (despite not knowing if the factors of `type(uint256).max` are contained
/// in x & y) and the minimum would be `type(uint256).min` (despite not knowing if `unchecked { type(uint256).max + 1 }`'s factors are contained in x & y). Therefore,
/// we have potentially underestimated the minimum and overestimated the maximum of the product. Factorization of large integers is untenable from a performance standpoint
/// so this concession on precision is accepted (and remains sound but can result in false positive analyses if depended on).
///
/// ### Note
/// Signed integers use 2's complement representation so the maximum is <code>2<sup>size - 1</sup> - 1</code>, while unsigned integers are <code>2<sup>size</sup> - 1</code>
///
///
/// ### Truth Tables
/// Truth table for `checked mul` operation:
///
///| Mul             | Uint                                                                                     | Int                                                                                      | BytesX | Address | Bytes | String |
///|-----------------|------------------------------------------------------------------------------------------|------------------------------------------------------------------------------------------|--------|---------|-------|--------|
///| **Uint**        | min: lhs<sub>min</sub> * rhs<sub>min</sub><br>max: lhs<sub>max</sub> * rhs<sub>max</sub> | min: lhs<sub>min</sub> * rhs<sub>min</sub><br>max: lhs<sub>max</sub> * rhs<sub>max</sub> | N/A    | N/A     | N/A   | N/A    |
///| **Int**         | min: lhs<sub>min</sub> * rhs<sub>min</sub><br>max: lhs<sub>max</sub> * rhs<sub>max</sub> | min: lhs<sub>min</sub> * rhs<sub>min</sub><br>max: lhs<sub>max</sub> * rhs<sub>max</sub> | N/A    | N/A     | N/A   | N/A    |
///| **BytesX**      | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **Address**     | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **Bytes**       | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///| **String**      | N/A                                                                                      | N/A                                                                                      | N/A    | N/A     | N/A   | N/A    |
///
/// Truth table for `wrapping mul` operation:
///
/// `todo!()`
///
// | Wrapping Mul              | Uint                                                                                                                                    | Int                                                                                                                   | BytesX | Address | Bytes | String |
// |---------------------------|-----------------------------------------------------------------------------------------------------------------------------------------|-----------------------------------------------------------------------------------------------------------------------|--------|---------|-------|--------|
// | **Uint**                  | min: {0, lhs<sub>min</sub> * rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> * rhs<sub>max</sub>}                   | min: {0, lhs<sub>min</sub> + rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>} | N/A    | N/A     | N/A   | N/A    |
// | **Int**                   | min: {<br>&nbsp;&nbsp;&nbsp;-2<sup>size-1</sup>,<br>&nbsp;&nbsp;&nbsp;lhs<sub>min</sub> * rhs<sub>min</sub>,<br>&nbsp;&nbsp;&nbsp;lhs<sub>min</sub> * rhs<sub>max</sub>,<br>&nbsp;&nbsp;&nbsp;lhs<sub>max</sub> * rhs<sub>min</sub><br>}<br>max: {<br>&nbsp;&nbsp;&nbsp;2<sup>size</sup> - 1,<br>&nbsp;&nbsp;&nbsp;lhs<sub>max</sub> * rhs<sub>max</sub><br>} | min: {0, lhs<sub>min</sub> * rhs<sub>min</sub>}<br>max: {2<sup>size</sup> - 1, lhs<sub>max</sub> + rhs<sub>max</sub>} | N/A    | N/A     | N/A   | N/A    |
// | **BytesX**                | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
// | **Address**               | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
// | **Bytes**                 | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
// | **String**                | N/A                                                                                                                                     | N/A                                                                                                                   | N/A    | N/A     | N/A   | N/A    |
pub fn exec_mul(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    wrapping: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    let mut candidates = vec![];
    let saturating_mul = |lhs: &Elem<_>, rhs: &Elem<_>, candidates: &mut Vec<Elem<Concrete>>| {
        if let Some(c) = lhs.range_mul(rhs) {
            candidates.push(c);
        }
    };

    if wrapping {
        let zero = Elem::from(Concrete::from(U256::zero()));
        let mut all_overflowed = true;
        let mut one_overflowed = false;
        let add_candidate = |lhs: &Elem<Concrete>,
                             rhs: &Elem<Concrete>,
                             candidates: &mut Vec<Elem<Concrete>>,
                             all_overflowed: &mut bool,
                             one_overflowed: &mut bool| {
            if let Some(c) = lhs.range_wrapping_mul(rhs) {
                if !matches!(
                    lhs.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Equal)
                ) {
                    let reverse = c.range_div(lhs).unwrap();
                    let overflowed = !matches!(
                        reverse.range_ord(rhs, analyzer).unwrap(),
                        std::cmp::Ordering::Equal
                    );
                    if *all_overflowed && !overflowed {
                        *all_overflowed = false;
                    }

                    if !*one_overflowed && overflowed {
                        *one_overflowed = true;
                    }
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
        );
        add_candidate(
            lhs_min,
            rhs_max,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
        );
        add_candidate(
            lhs_max,
            rhs_min,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
        );
        add_candidate(
            lhs_max,
            rhs_max,
            &mut candidates,
            &mut all_overflowed,
            &mut one_overflowed,
        );

        if all_overflowed || one_overflowed {
            // We overflowed in every case, or had a conditional overflow.
            // In this case we just under/overestimate
            saturating_mul(lhs_max, rhs_max, &mut candidates);
            saturating_mul(lhs_min, rhs_min, &mut candidates);
            saturating_mul(lhs_min, rhs_max, &mut candidates);
            saturating_mul(lhs_max, rhs_min, &mut candidates);

            let add_min = |elem: &Elem<Concrete>, candidates: &mut Vec<Elem<_>>| {
                if let Some(c) = elem.maybe_concrete() {
                    if let Some(min) = Concrete::min_of_type(&c.val) {
                        candidates.push(RangeConcrete::new(min, c.loc).into());
                    }
                }
            };
            // We are able to conditionally overflow, so add min of both types
            add_min(lhs_min, &mut candidates);
            add_min(lhs_max, &mut candidates);
            add_min(rhs_min, &mut candidates);
            add_min(rhs_max, &mut candidates);
        }
    } else {
        // without inspecting types of lhs and rhs, its easiest just to run them all and
        // sort
        saturating_mul(lhs_min, rhs_min, &mut candidates);
        saturating_mul(lhs_min, rhs_max, &mut candidates);
        saturating_mul(lhs_max, rhs_min, &mut candidates);
        saturating_mul(lhs_max, rhs_max, &mut candidates);
    }

    // Sort the candidates
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DummyGraph;
    use ethers_core::types::U256;
    use solang_parser::pt::Loc;

    #[test]
    fn sized_uint_uint() {
        let x = rc_uint_sized(255);
        let y = rc_uint_sized(255);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(255)));
    }

    #[test]
    fn sized_wrapping_uint_uint() {
        let x = rc_uint_sized(255);
        let y = rc_uint_sized(255);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(1)));
    }

    #[test]
    fn sized_int_int() {
        let x = rc_int_sized(-127);
        let y = rc_int_sized(-127);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(127i32)));
    }

    #[test]
    fn sized_int_int_one() {
        let x = rc_int_sized(-1);
        let y = rc_int_sized(-128);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(127i32)));
    }

    #[test]
    fn sized_int_uint() {
        let x = rc_int_sized(-127);
        let y = rc_int_sized(127);
        let y2 = rc_uint_sized(127);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        let result2 = x.range_mul(&y2).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }
    #[test]
    fn sized_uint_int() {
        let x = rc_int_sized(127);
        let x2 = rc_uint_sized(127);
        let y = rc_int_sized(-127);
        let result = x.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        let result2 = x2.range_mul(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn sized_wrapping_int_int() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(1i32)));
    }

    #[test]
    fn sized_wrapping_int_uint() {
        let x = RangeConcrete::new(Concrete::Int(8, I256::from(-127i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(127i32)), Loc::Implicit);
        let result = x
            .range_wrapping_mul(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        let y2 = RangeConcrete::new(Concrete::Uint(8, U256::from(127i32)), Loc::Implicit);
        let result2 = x
            .range_wrapping_mul(&y2)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result, result2);
        assert_eq!(result.val, Concrete::Int(8, I256::from(-1i32)));
    }

    #[test]
    fn exec_sized_uint_uint_saturating() {
        let g = DummyGraph::default();
        let lhs_min = rc_uint_sized(5).into();
        let lhs_max = rc_uint_sized(15).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(20).into();

        let max_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, false, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, false, false, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(5)));
    }

    #[test]
    fn exec_sized_wrapping_uint_uint_no_overflow() {
        let g = DummyGraph::default();
        let lhs_min = rc_uint_sized(5).into();
        let lhs_max = rc_uint_sized(15).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(16).into();

        let max_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(240)));
        let min_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(5)));
    }

    #[test]
    fn exec_sized_wrapping_uint_uint_full_overflow() {
        let g = DummyGraph::default();
        let lhs_min = rc_uint_sized(126).into();
        let lhs_max = rc_uint_sized(127).into();
        let rhs_min = rc_uint_sized(252).into();
        let rhs_max = rc_uint_sized(255).into();

        let max_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        // we just have to overestimate
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(255)));
        let min_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        // we just have to underestimate
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(0)));
    }

    #[test]
    fn exec_sized_wrapping_int_uint_cond_overflow() {
        let g = DummyGraph::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(127).into();
        let rhs_min = rc_uint_sized(0).into();
        let rhs_max = rc_uint_sized(255).into();

        let max_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn exec_sized_wrapping_int_uint_no_overflow() {
        let g = DummyGraph::default();
        let lhs_min = rc_int_sized(-5).into();
        let lhs_max = rc_int_sized(5).into();
        let rhs_min = rc_uint_sized(0).into();
        let rhs_max = rc_uint_sized(3).into();

        let max_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(15i32)));
        let min_result = exec_mul(&lhs_min, &lhs_max, &rhs_min, &rhs_max, false, true, &g)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-15i32)));
    }
}
