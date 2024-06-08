use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use ethers_core::types::{I256, U256};

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
                            let op_res = val.saturating_sub(I256::from_raw(rhs_val));
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

                    let op_res = val.saturating_add(neg_v.into_raw()).min(max);
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
                    let op_res = l.saturating_sub(*r);
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
                            let val = Concrete::Int(size, op_res);
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
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => Some(Elem::Concrete(
                    RangeConcrete::new(Concrete::Int(*lhs_size, l.overflowing_sub(*r).0), self.loc),
                )),
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
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    // quick check if rhs is const and zero, if so return min or max
    if wrapping {
        let mut candidates = vec![];
        let mut all_overflowed = true;
        let mut one_overflowed = false;
        let add_candidate = |lhs: &Elem<Concrete>,
                             rhs: &Elem<Concrete>,
                             candidates: &mut Vec<Elem<Concrete>>,
                             all_overflowed: &mut bool,
                             one_overflowed: &mut bool| {
            if let Some(c) = lhs.range_wrapping_sub(rhs) {
                let overflowed = matches!(
                    c.range_ord(lhs, analyzer),
                    Some(std::cmp::Ordering::Greater)
                );

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
    } else if maximize {
        // if we are maximizing, the largest value will always just be the the largest value - the smallest value
        lhs_max.range_sub(rhs_min)
    } else {
        // if we are minimizing, the smallest value will always be smallest value - largest value
        lhs_min.range_sub(rhs_max)
    }
}
