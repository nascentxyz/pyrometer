use crate::nodes::Concrete;
use range::{elem::*, exec::*};

use ethers_core::types::{H256, U256};
use std::collections::BTreeMap;

impl RangeConcat<Concrete> for RangeConcrete<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete {
            val: self.val.clone().concat(&other.val)?,
            loc: self.loc,
        }))
    }
}

impl RangeConcat<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_concat(&self, other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        match (other.val.clone(), self.val.iter().take(1).next()) {
            (
                Concrete::DynBytes(val),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            )
            | (Concrete::DynBytes(val), None) => {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let idx = last.clone() + idx;
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::from(val.len()))),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (
                Concrete::String(val),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::String(..),
                        ..
                    }),
                )),
            )
            | (Concrete::String(val), None) => {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let new = val
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let idx = last.clone() + idx;
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (idx, v)
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::from(val.len()))),
                    val: existing,
                    loc: other.loc,
                })))
            }
            _e => None,
        }
    }
}

impl RangeConcat<Concrete, RangeDyn<Concrete>> for RangeDyn<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        let val: Option<(_, &Elem<Concrete>)> = self.val.iter().take(1).next();
        let o_val: Option<(_, &Elem<Concrete>)> = other.val.iter().take(1).next();
        match (val, o_val) {
            (
                Some((
                    _,
                    &Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    &Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            ) => {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let other_vals = other
                    .val
                    .clone()
                    .into_iter()
                    .map(|(i, v)| (i + last.clone(), v))
                    .collect::<BTreeMap<_, _>>();

                existing.extend(other_vals);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: self.len.clone() + other.len.clone(),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (Some((_, l @ Elem::Reference(_))), None) => Some(l.clone()),
            (None, Some((_, r @ Elem::Reference(_)))) => Some(r.clone()),
            (None, None) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            _e => None,
        }
    }
}

impl RangeConcat<Concrete> for Elem<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_concat(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => a.range_concat(&**b),
            (Elem::Concrete(c), Elem::ConcreteDyn(d))
            | (Elem::ConcreteDyn(d), Elem::Concrete(c)) => d.range_concat(c),
            _e => None,
        }
    }
}