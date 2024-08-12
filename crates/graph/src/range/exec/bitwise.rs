use crate::nodes::{Builtin, Concrete};
use crate::range::{elem::*, exec_traits::*};

use shared::RangeArena;

use ethers_core::types::{H256, I256, U256};

impl RangeBitwise<Concrete> for RangeConcrete<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Uint(s, u), Concrete::Int(s2, i))
            | (Concrete::Int(s, i), Concrete::Uint(s2, u)) => {
                let op_res = *u & i.into_raw();
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a & b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::DynBytes(v), _) if v.len() <= 32 => RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )
            .range_bit_and(other),
            (_, Concrete::DynBytes(v)) if v.len() <= 32 => self.range_bit_and(&RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )),
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l & r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
        }
    }

    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a | b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::DynBytes(v), _) if v.len() <= 32 => RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )
            .range_bit_or(other),
            (_, Concrete::DynBytes(v)) if v.len() <= 32 => self.range_bit_or(&RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )),
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l | r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
        }
    }

    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (i @ Concrete::Int(s, ..), u @ Concrete::Uint(..)) => {
                let i_b = i.bit_representation().unwrap().uint_val().unwrap();
                let u_b = u.uint_val().unwrap();
                let op_res = i_b ^ u_b;
                let val = Concrete::Uint(256, op_res).cast(i.as_builtin()).unwrap();
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a ^ b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::DynBytes(v), _) if v.len() <= 32 => RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )
            .range_bit_xor(other),
            (_, Concrete::DynBytes(v)) if v.len() <= 32 => self.range_bit_xor(&RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )),
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l ^ r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
        }
    }

    fn range_bit_not(&self) -> Option<Elem<Concrete>> {
        match &self.val {
            Concrete::Uint(size, a) => {
                let max = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .uint_val()
                    .unwrap();
                let val = U256(
                    a.0.into_iter()
                        .map(|i| !i)
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                );
                let op_res = val & max;
                let rc = RangeConcrete::new(Concrete::Uint(*size, op_res), self.loc);
                Some(rc.into())
            }
            Concrete::Int(size, a) => {
                let (op_res, _) = a.overflowing_neg();
                let (op_res, _) = op_res.overflowing_sub(1.into());
                let rc = RangeConcrete::new(Concrete::Int(*size, op_res), self.loc);
                Some(rc.into())
            }
            Concrete::Bytes(s, a) => {
                let mut op_res = H256::default();
                (0..*s).for_each(|i| {
                    op_res.0[i as usize] = !a.0[i as usize];
                });
                let rc = RangeConcrete::new(Concrete::Bytes(*s, op_res), self.loc);
                Some(rc.into())
            }
            Concrete::DynBytes(v) if v.len() <= 32 => RangeConcrete::new(
                Concrete::DynBytes(v.clone()).cast(Builtin::Bytes(v.len() as u8))?,
                self.loc,
            )
            .range_bit_not(),
            _ => None,
        }
    }
}

impl RangeBitwise<Concrete> for Elem<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_and(b),
            _ => None,
        }
    }
    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_or(b),
            _ => None,
        }
    }
    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_xor(b),
            _ => None,
        }
    }

    fn range_bit_not(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => a.range_bit_not(),
            _ => None,
        }
    }
}

/// Executes a bitwise `and` given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
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
pub fn exec_bit_and(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    match (lhs_min, lhs_max, rhs_min, rhs_max) {
        (Elem::ConcreteDyn(d), _, _, _) => {
            return exec_bit_and(
                &d.as_sized_bytes()?,
                lhs_max,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, Elem::ConcreteDyn(d), _, _) => {
            return exec_bit_and(
                lhs_min,
                &d.as_sized_bytes()?,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, Elem::ConcreteDyn(d), _) => {
            return exec_bit_and(
                lhs_min,
                lhs_max,
                &d.as_sized_bytes()?,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, _, Elem::ConcreteDyn(d)) => {
            return exec_bit_and(
                lhs_min,
                lhs_max,
                rhs_min,
                &d.as_sized_bytes()?,
                maximize,
                arena,
            );
        }
        _ => {}
    }

    let mut candidates = vec![];
    let bit_and = |lhs: &Elem<_>, rhs: &Elem<_>, candidates: &mut Vec<Elem<Concrete>>| {
        if let Some(c) = lhs.range_bit_and(rhs) {
            candidates.push(c);
        }
    };

    // the max is the min of the maxes
    match lhs_max.range_ord(rhs_max, arena) {
        Some(std::cmp::Ordering::Less) => {
            candidates.push(lhs_max.clone());
        }
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal) => {
            candidates.push(rhs_max.clone());
        }
        _ => {}
    }

    bit_and(lhs_min, rhs_min, &mut candidates);
    bit_and(lhs_min, rhs_max, &mut candidates);
    bit_and(lhs_max, rhs_min, &mut candidates);
    bit_and(lhs_max, rhs_max, &mut candidates);

    let zero = Elem::from(Concrete::from(U256::from(0)));
    let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

    let min_contains = matches!(
        rhs_min.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        candidates.push(zero);
    }

    let min_contains = matches!(
        rhs_min.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        candidates.push(lhs_min.clone());
        candidates.push(lhs_max.clone());
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

/// Executes a bitwise `or` given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
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
pub fn exec_bit_or(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    match (lhs_min, lhs_max, rhs_min, rhs_max) {
        (Elem::ConcreteDyn(d), _, _, _) => {
            return exec_bit_or(
                &d.as_sized_bytes()?,
                lhs_max,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, Elem::ConcreteDyn(d), _, _) => {
            return exec_bit_or(
                lhs_min,
                &d.as_sized_bytes()?,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, Elem::ConcreteDyn(d), _) => {
            return exec_bit_or(
                lhs_min,
                lhs_max,
                &d.as_sized_bytes()?,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, _, Elem::ConcreteDyn(d)) => {
            return exec_bit_or(
                lhs_min,
                lhs_max,
                rhs_min,
                &d.as_sized_bytes()?,
                maximize,
                arena,
            );
        }
        _ => {}
    }

    let mut candidates = vec![];
    let bit_or = |lhs: &Elem<_>, rhs: &Elem<_>, candidates: &mut Vec<Elem<Concrete>>| {
        if let Some(c) = lhs.range_bit_or(rhs) {
            candidates.push(c);
        }
    };

    bit_or(lhs_min, rhs_min, &mut candidates);
    bit_or(lhs_min, rhs_max, &mut candidates);
    bit_or(lhs_max, rhs_min, &mut candidates);
    bit_or(lhs_max, rhs_max, &mut candidates);

    let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

    let min_contains = matches!(
        rhs_min.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        candidates.push(negative_one.clone());
        candidates.push(negative_one.clone());
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

/// Executes a bitwise `xor` given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
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
pub fn exec_bit_xor(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    match (lhs_min, lhs_max, rhs_min, rhs_max) {
        (Elem::ConcreteDyn(d), _, _, _) => {
            return exec_bit_xor(
                &d.as_sized_bytes()?,
                lhs_max,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, Elem::ConcreteDyn(d), _, _) => {
            return exec_bit_xor(
                lhs_min,
                &d.as_sized_bytes()?,
                rhs_min,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, Elem::ConcreteDyn(d), _) => {
            return exec_bit_xor(
                lhs_min,
                lhs_max,
                &d.as_sized_bytes()?,
                rhs_max,
                maximize,
                arena,
            );
        }
        (_, _, _, Elem::ConcreteDyn(d)) => {
            return exec_bit_xor(
                lhs_min,
                lhs_max,
                rhs_min,
                &d.as_sized_bytes()?,
                maximize,
                arena,
            );
        }
        _ => {}
    }

    println!("lhs_min: {lhs_min}");
    println!("lhs_max: {lhs_max}");
    println!("rhs_min: {rhs_min}");
    println!("rhs_max: {rhs_max}");

    let mut candidates = vec![
        lhs_min.range_bit_xor(rhs_min),
        lhs_min.range_bit_xor(rhs_max),
        lhs_max.range_bit_xor(rhs_min),
        lhs_max.range_bit_xor(rhs_max),
    ];

    println!(
        "candidates: {:#?}",
        candidates
            .iter()
            .map(|i| format!("{}", i.as_ref().unwrap()))
            .collect::<Vec<_>>()
    );

    let zero = Elem::from(Concrete::from(U256::from(0)));
    let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

    let min_contains = matches!(
        rhs_min.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        // if the rhs contains zero, in xor, thats just itself
        candidates.push(lhs_max.range_bit_xor(&zero));
    }

    let min_contains = matches!(
        rhs_min.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        rhs_max.range_ord(&negative_one, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        candidates.push(lhs_min.range_bit_xor(&negative_one));
        candidates.push(lhs_max.range_bit_xor(&negative_one));
    }

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

/// Executes a bitwise `not` given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
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
pub fn exec_bit_not(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    maximize: bool,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    match (lhs_min, lhs_max) {
        (Elem::ConcreteDyn(d), _) => {
            return exec_bit_not(&d.as_sized_bytes()?, lhs_max, maximize, arena);
        }
        (_, Elem::ConcreteDyn(d)) => {
            return exec_bit_not(lhs_min, &d.as_sized_bytes()?, maximize, arena);
        }
        _ => {}
    }
    let mut candidates = vec![lhs_min.range_bit_not(), lhs_max.range_bit_not()];

    let zero = Elem::from(Concrete::from(U256::from(0)));

    let min_contains = matches!(
        lhs_min.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
    );

    let max_contains = matches!(
        lhs_max.range_ord(&zero, arena),
        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
    );

    if min_contains && max_contains {
        match lhs_min {
            Elem::Concrete(
                ref r @ RangeConcrete {
                    val: Concrete::Uint(..),
                    ..
                },
            ) => candidates.push(Some(Concrete::max_of_type(&r.val).unwrap().into())),
            Elem::Concrete(
                ref r @ RangeConcrete {
                    val: Concrete::Int(..),
                    ..
                },
            ) => candidates.push(Some(Concrete::min_of_type(&r.val).unwrap().into())),
            _ => {}
        }
    }

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
    use solang_parser::pt::Loc;

    #[test]
    fn and_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(5)));
    }

    #[test]
    fn and_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-15)));
    }

    #[test]
    fn and_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::from(h2));
    }

    #[test]
    fn or_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(15)));
    }

    #[test]
    fn or_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-5)));
    }

    #[test]
    fn or_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::from(h));
    }

    #[test]
    fn xor_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(10)));
    }

    #[test]
    fn xor_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(10)));
    }

    #[test]
    fn xor_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();

        let mut expected: [u8; 32] = [0; 32];
        expected[0..3].copy_from_slice(&[1, 0, 1][..]);
        assert_eq!(result.val, Concrete::from(expected));
    }

    #[test]
    fn not_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX << 4));
    }

    #[test]
    fn not_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(14)));
    }

    #[test]
    fn not_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1; 4][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();

        let mut expected: [u8; 32] = [255; 32];
        expected[0..4].copy_from_slice(&[254, 254, 254, 254][..]);
        assert_eq!(result.val, Concrete::from(expected));
    }
}
