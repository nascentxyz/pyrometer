use crate::nodes::Concrete;
use range::{elem::*, exec::*};

use ethers_core::types::{H256, U256};
use std::collections::BTreeMap;

impl RangeCast<Concrete> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete {
            val: self.val.clone().cast_from(&other.val)?,
            loc: self.loc,
        }))
    }
}

impl RangeCast<Concrete, Box<RangeDyn<Concrete>>> for RangeConcrete<Concrete> {
    fn range_cast(&self, other: &Box<RangeDyn<Concrete>>) -> Option<Elem<Concrete>> {
        match (self.val.clone(), other.val.iter().take(1).next()) {
            (
                Concrete::Bytes(size, val),
                Some((
                    _,
                    Elem::Concrete(Self {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            )
            | (Concrete::Bytes(size, val), None) => {
                let mut existing = other.val.clone();
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
                existing.extend(new);
                Some(Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::from(size))),
                    val: existing,
                    loc: other.loc,
                })))
            }
            (
                Concrete::DynBytes(val),
                Some((
                    _,
                    Elem::Concrete(Self {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
            )
            | (Concrete::DynBytes(val), None) => {
                let mut existing = other.val.clone();
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
                    Elem::Concrete(Self {
                        val: Concrete::String(..),
                        ..
                    }),
                )),
            )
            | (Concrete::String(val), None) => {
                let mut existing = other.val.clone();
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

impl RangeCast<Concrete, RangeDyn<Concrete>> for RangeDyn<Concrete> {
    fn range_cast(&self, other: &Self) -> Option<Elem<Concrete>> {
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
            )
            | (
                Some((
                    _,
                    &Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }),
                )),
                None,
            ) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(..),
                        ..
                    }),
                )),
            )
            | (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(..),
                        ..
                    }),
                )),
                None,
            ) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(..),
                        ..
                    }),
                )),
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(..),
                        ..
                    }),
                )),
            )
            | (
                Some((
                    _,
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(..),
                        ..
                    }),
                )),
                None,
            ) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            (Some((_, l @ Elem::Reference(_))), None) => Some(l.clone()),
            (None, Some((_, r @ Elem::Reference(_)))) => Some(r.clone()),
            (None, None) => Some(Elem::ConcreteDyn(Box::new(self.clone()))),
            _e => None,
        }
    }
}

impl RangeCast<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_cast(&self, other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        let (_k, val): (_, &Elem<Concrete>) = self.val.iter().take(1).next()?;
        let o_val = &other.val;
        // println!("HERE {:?} {:?} {:?}", k, val, o_val);
        match (val, o_val) {
            (
                &Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(1, ..),
                    ..
                }),
                Concrete::Bytes(size, _),
            ) => {
                let mut h = H256::default();
                for (i, (_, val)) in self.val.iter().take(*size as usize).enumerate() {
                    match val {
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Bytes(1, v),
                            ..
                        }) => {
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