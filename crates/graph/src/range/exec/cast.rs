use crate::nodes::{Builtin, Concrete};
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use ethers_core::types::{H256, U256};
use std::collections::BTreeMap;

impl RangeCast<Concrete> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete::new(
            self.val.clone().cast_from(&other.val)?,
            self.loc,
        )))
    }
}

impl RangeCast<Concrete, RangeDyn<Concrete>> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        match (
            self.val.clone(),
            other.val.values().take(1).next().map(|(a, _)| a),
        ) {
            (Concrete::Uint(size, val), o) if o.is_none() || o.unwrap().is_bytes() => {
                RangeConcrete::new(
                    Concrete::Uint(size, val).cast(Builtin::Bytes((size / 8) as u8))?,
                    self.loc,
                )
                .range_cast(other)
            }
            (Concrete::Bytes(size, val), o) if o.is_none() || o.unwrap().is_bytes() => {
                let new = val
                    .0
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                Some(Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::from(size))),
                    new,
                    other.loc,
                )))
            }
            (Concrete::DynBytes(val), o) if o.is_none() || o.unwrap().is_bytes() => {
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                Some(Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::from(val.len()))),
                    new,
                    other.loc,
                )))
            }
            (Concrete::String(val), o) if o.is_none() || o.unwrap().is_string() => {
                let new = val
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                Some(Elem::ConcreteDyn(RangeDyn::new(
                    Elem::from(Concrete::from(U256::from(val.len()))),
                    new,
                    other.loc,
                )))
            }
            _e => None,
        }
    }
}

impl RangeCast<Concrete, RangeDyn<Concrete>> for RangeDyn<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        let val: Option<&Elem<Concrete>> = self.val.values().take(1).next().map(|(a, _)| a);
        let o_val: Option<&Elem<Concrete>> = other.val.values().take(1).next().map(|(a, _)| a);

        match (val, o_val) {
            (Some(elem), Some(o_elem))
                if elem.is_bytes() && o_elem.is_bytes()
                    || elem.is_uint() && o_elem.is_uint()
                    || elem.is_int() && o_elem.is_int() =>
            {
                Some(Elem::ConcreteDyn(self.clone()))
            }
            (Some(elem), None) if elem.is_bytes() || elem.is_uint() || elem.is_int() => {
                Some(Elem::ConcreteDyn(self.clone()))
            }
            (Some(Elem::Reference(_)), None) => Some(Elem::ConcreteDyn(self.clone())),
            (None, Some(Elem::Reference(_))) => Some(Elem::ConcreteDyn(self.clone())),
            (None, None) => Some(Elem::ConcreteDyn(self.clone())),
            _ => None,
        }
    }
}

impl RangeCast<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_cast(&self, other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        let val: &Elem<_> = self.val.values().take(1).next().map(|(a, _)| a)?;
        let o_val = &other.val;
        match (val, o_val) {
            (
                &Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(1, ..),
                    ..
                }),
                Concrete::Bytes(size, _),
            ) => {
                let mut h = H256::default();
                for (i, val) in self.val.values().take(*size as usize).enumerate() {
                    match val {
                        (
                            Elem::Concrete(RangeConcrete {
                                val: Concrete::Bytes(1, v),
                                ..
                            }),
                            _,
                        ) => {
                            // consume as many as we can
                            h.0[i] = v.0[0];
                        }
                        _ => break,
                    }
                }
                Some(Elem::Concrete(Concrete::Bytes(*size, h).into()))
            }
            _e => None,
        }
    }
}

impl RangeCast<Concrete> for Elem<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_cast(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => {
                // super dumb type stuff here that makes it so we have to specify
                <RangeDyn<Concrete> as RangeCast<Concrete>>::range_cast(a, b)
            }
            (Elem::ConcreteDyn(a), Elem::Concrete(b)) => a.range_cast(b),
            (Elem::Concrete(a), Elem::ConcreteDyn(b)) => a.range_cast(b),
            _e => None,
        }
    }
}

pub fn exec_cast(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    // the weird thing about cast is that we really dont know until after the cast due to sizing things
    // so we should just try them all then compare
    let candidates = vec![
        lhs_min.range_cast(rhs_min),
        lhs_min.range_cast(rhs_max),
        lhs_max.range_cast(rhs_min),
        lhs_max.range_cast(rhs_max),
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
    use ethers_core::types::I256;
    use solang_parser::pt::Loc;

    #[test]
    fn int_downcast() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-1500)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(8, I256::from(0)), Loc::Implicit);
        let result = x.range_cast(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(8, I256::from(36)));
    }

    #[test]
    fn uint_downcast() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(1500)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(8, U256::from(0)), Loc::Implicit);
        let result = x.range_cast(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(8, U256::from(220)));
    }

    #[test]
    fn int_weirdness() {
        // type(int64).max
        let v = Concrete::max_of_type(&Concrete::Int(64, I256::from(0i32)))
            .unwrap()
            .int_val()
            .unwrap();
        // int128(type(int64).max)
        let x = RangeConcrete::new(Concrete::Int(128, v), Loc::Implicit);
        // int128(type(int64).max) + 1
        let x = x
            .range_add(&RangeConcrete::new(
                Concrete::Int(256, I256::from(1)),
                Loc::Implicit,
            ))
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        let expected = x.val.int_val().unwrap() * I256::from(-1i32);
        let y = RangeConcrete::new(Concrete::Int(64, I256::from(0)), Loc::Implicit);
        // int64(int128(type(int64).max) + 1)
        let result = x.range_cast(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(64, expected));
    }

    #[test]
    fn int_upcast() {
        let x = rc_int_sized(-101);
        let y = rc_int256(-101);
        let result = x.range_cast(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-101)));
    }

    #[test]
    fn bytes_upcast() {
        let x = RangeConcrete::new(Concrete::from(vec![19, 55]), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(vec![0, 0, 0, 0]), Loc::Implicit);
        let result = x.range_cast(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::from(vec![19, 55, 0, 0]));
    }
}
