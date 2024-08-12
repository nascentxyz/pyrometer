use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use ethers_core::types::{I256, U256};

impl RangeMod<Concrete> for RangeConcrete<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                if rhs_val == 0.into() {
                    return None;
                }
                let op_res = lhs_val % rhs_val;
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, neg_v)) => {
                    let op_res = I256::from_raw(*val) % *neg_v;
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, val)) if *val != 0.into() => {
                    let op_res = *neg_v % I256::from_raw(*val);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    // the wrapping never actually occurs mathematically. See ethers-rs docs for more info
                    let op_res = l.wrapping_rem(*r);
                    let val = Concrete::Int(*lhs_size, op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeMod<Concrete> for Elem<Concrete> {
    fn range_mod(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_mod(b),
            _ => None,
        }
    }
}

/// Executes an modulus given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
///
/// ### Note
/// Signed integers use 2's complement representation so the maximum is <code>2<sup>size - 1</sup> - 1</code>, while unsigned integers are <code>2<sup>size</sup> - 1</code>
///
///
/// ### Truth Tables
/// Truth table for `checked mod` operation:
///
/// `todo!()`
pub fn exec_mod(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let is_const = |l: &Elem<_>, r: &Elem<_>, arena: &mut RangeArena<Elem<_>>| -> bool {
        matches!(l.range_ord(r, arena), Some(std::cmp::Ordering::Equal))
    };

    if is_const(lhs_min, lhs_max, arena) && is_const(rhs_min, rhs_max, arena) {
        return lhs_min.range_mod(rhs_min);
    }

    let zero = Elem::from(Concrete::from(U256::zero()));

    let lhs_min_is_pos = matches!(
        lhs_min.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
    );

    let lhs_max_is_pos = matches!(
        lhs_max.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
    );
    let mod_min_is_pos = matches!(
        rhs_min.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
    );

    let mod_max_is_pos = matches!(
        rhs_max.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater)
    );

    // check if all lhs values are less than rhs values
    if maximize
        && lhs_max_is_pos
        && mod_max_is_pos
        && matches!(
            lhs_max.range_ord(rhs_max, arena),
            Some(std::cmp::Ordering::Less)
        )
    {
        // the lhs is entirely smaller than the modulo, so its effectively a noop, just return
        // the min or max
        return Some(lhs_max.clone());
    }

    let mut candidates = vec![];
    let one = Elem::from(Concrete::from(U256::from(1)));
    let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));
    if !mod_min_is_pos {
        if let Some(r) = rhs_min.range_add(&one) {
            candidates.push(r);
        }
    } else if let Some(r) = rhs_min.range_sub(&one) {
        candidates.push(r);
    }

    if !mod_max_is_pos {
        if let Some(r) = rhs_max.range_add(&one) {
            candidates.push(r);
        }
    } else if let Some(r) = rhs_max.range_sub(&one) {
        candidates.push(r);
    }

    if !lhs_min_is_pos {
        if let Some(neg_max) = rhs_max.range_mul(&negative_one) {
            match neg_max.range_ord(lhs_min, arena) {
                None => {}
                Some(std::cmp::Ordering::Less) => candidates.push(lhs_min.clone()),
                Some(std::cmp::Ordering::Greater) => {
                    candidates.push(neg_max.range_add(&one).unwrap())
                }
                _ => candidates.push(lhs_min.clone()),
            }
        }
    }

    candidates.push(zero);

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
    use solang_parser::pt::Loc;

    #[test]
    fn uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(17)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(2)));
    }

    #[test]
    fn uint_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(17)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(5i32)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(2)));
    }

    #[test]
    fn uint_neg_int() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(17)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(2)));
    }

    #[test]
    fn neg_int_uint() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-17i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-2i32)));
    }

    #[test]
    fn neg_int_neg_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-17i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-2i32)));
    }

    #[test]
    fn uint_zero() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(17)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(0)), Loc::Implicit);
        assert!(x.range_mod(&y).is_none());
    }

    #[test]
    fn int_zero() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-17i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(0)), Loc::Implicit);
        assert!(x.range_mod(&y).is_none());
    }

    #[test]
    fn int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::MIN), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-1i32)), Loc::Implicit);
        let result = x.range_mod(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(0i32)));
    }

    #[test]
    fn exec_sized_uint_uint_1() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(5).into();
        let lhs_max = rc_uint_sized(15).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(20).into();

        let max_result = exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(15)));
        let min_result = exec_mod(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(0)));
    }

    #[test]
    fn exec_sized_uint_uint_2() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint_sized(16).into();
        let lhs_max = rc_uint_sized(160).into();
        let rhs_min = rc_uint_sized(1).into();
        let rhs_max = rc_uint_sized(16).into();

        let max_result = exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Uint(8, U256::from(15)));
        let min_result = exec_mod(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(8, U256::from(0)));
    }

    #[test]
    fn exec_sized_int_uint() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(127).into();
        let rhs_min = rc_uint_sized(0).into();
        let rhs_max = rc_uint_sized(255).into();

        let max_result = exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(127i32)));
        let min_result = exec_mod(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-128i32)));
    }

    #[test]
    fn exec_sized_int_int_max() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_int_sized(-128).into();
        let lhs_max = rc_int_sized(-100).into();
        let rhs_min = rc_int_sized(-5).into();
        let rhs_max = rc_int_sized(5).into();

        let max_result = exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        // TODO: improve mod calc to consider lhs being entirely negative
        // assert_eq!(max_result.val, Concrete::Int(8, I256::from(0i32)));
        assert_eq!(max_result.val, Concrete::Int(8, I256::from(4i32)));
        let min_result = exec_mod(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Int(8, I256::from(-4i32)));
    }

    #[test]
    fn repro() {
        let max = U256::from_dec_str(
            "1340186218024493002587627141304258192746180378074543565271499814906382593",
        )
        .unwrap();

        let g = DummyGraph::default();
        let mut arena = Default::default();
        let lhs_min = rc_uint256(0).into();
        let lhs_max = RangeConcrete::new(Concrete::Uint(256, max), Loc::Implicit).into();
        let rhs_min = rc_uint256(7).into();
        let rhs_max = rc_uint256(7).into();

        let max_result = exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete()
            .unwrap();
        // TODO: improve mod calc to consider lhs being entirely negative
        // assert_eq!(max_result.val, Concrete::Int(8, I256::from(0i32)));
        assert_eq!(max_result.val, Concrete::Uint(256, U256::from(6)));
        let min_result = exec_mod(
            &lhs_min, &lhs_max, &rhs_min, &rhs_max, false, &g, &mut arena,
        )
        .unwrap()
        .maybe_concrete()
        .unwrap();
        assert_eq!(min_result.val, Concrete::Uint(256, U256::from(0)));
    }
}
