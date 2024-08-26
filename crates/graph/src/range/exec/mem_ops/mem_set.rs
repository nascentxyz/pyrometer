use crate::GraphBackend;
use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*},
};

use shared::RangeArena;

use alloy_primitives::{B256, U256};

use std::collections::BTreeMap;

impl RangeMemSet<Concrete> for RangeDyn<Concrete> {
    fn range_set_indices(&self, range: &Self) -> Option<Elem<Concrete>> {
        tracing::trace!("setting range indices for: {self:?} {range:?}");
        let mut new_val = self.val.clone();
        let mut op_num = self.op_num;
        range.val.iter().for_each(|(k, (v, _))| {
            op_num += 1;
            new_val.insert(k.clone(), (v.clone(), op_num));
        });

        println!("new val: {new_val:#?}");

        Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
            *self.len.clone(),
            new_val,
            range.loc,
        )))
    }

    fn range_set_length(&self, other: &Self) -> Option<Elem<Concrete>> {
        let mut a = self.clone();
        a.len.clone_from(&other.len);
        Some(Elem::ConcreteDyn(a))
    }
}

impl RangeMemSet<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_set_indices(&self, range: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        match (
            range.val.clone(),
            self.val.values().take(1).next().map(|(a, _)| a),
        ) {
            (Concrete::DynBytes(val), s) if s.is_none() || s.unwrap().is_bytes() => {
                let mut existing = self.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                        (
                            Elem::from(Concrete::from(U256::from(i))),
                            (v, self.op_num + i),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    *self.len.clone(),
                    existing,
                    range.loc,
                )))
            }
            (Concrete::String(val), s) if s.is_none() || s.unwrap().is_string() => {
                let mut existing = self.val.clone();
                let new = val
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                        (
                            Elem::from(Concrete::from(U256::from(i))),
                            (v, i + self.op_num),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    *self.len.clone(),
                    existing,
                    range.loc,
                )))
            }
            _e => None,
        }
    }

    fn range_set_length(&self, other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        let mut a = self.clone();
        a.len = Box::new(Elem::Concrete(other.clone()));
        Some(Elem::ConcreteDyn(a))
    }
}

impl RangeMemSet<Concrete> for RangeConcrete<Concrete> {
    fn range_set_indices(&self, range: &Self) -> Option<Elem<Concrete>> {
        let mut new_val = self.val.clone();
        new_val.set_indices(&range.val);
        Some(Elem::Concrete(RangeConcrete::new(new_val, range.loc)))
    }

    fn range_set_length(&self, other: &Self) -> Option<Elem<Concrete>> {
        match other.val.into_u256() {
            Some(len) if len <= U256::from(32) => match self.val {
                Concrete::DynBytes(ref val) => Some(Elem::Concrete(RangeConcrete::new(
                    Concrete::DynBytes({
                        let mut v = val.clone();
                        v.resize(len.try_into().unwrap(), 0);
                        v
                    }),
                    self.loc,
                ))),
                Concrete::String(ref val) => Some(Elem::Concrete(RangeConcrete::new(
                    Concrete::String({
                        let mut v = val.clone();
                        let len: usize = len.try_into().unwrap();
                        v.push_str(&" ".repeat(len - v.chars().count()));
                        v
                    }),
                    self.loc,
                ))),
                Concrete::Bytes(_, val) => Some(Elem::Concrete(RangeConcrete::new(
                    Concrete::Bytes(len.try_into().unwrap(), val),
                    self.loc,
                ))),
                _ => None,
            },
            _ => {
                let new = match self.val {
                    Concrete::DynBytes(ref val) => Some(
                        val.iter()
                            .enumerate()
                            .map(|(i, v)| {
                                let mut bytes = [0x00; 32];
                                bytes[0] = *v;
                                let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                                (Elem::from(Concrete::from(U256::from(i))), (v, i))
                            })
                            .collect::<BTreeMap<_, _>>(),
                    ),
                    Concrete::String(ref val) => Some(
                        val.chars()
                            .enumerate()
                            .map(|(i, v)| {
                                let mut bytes = [0x00; 32];
                                v.encode_utf8(&mut bytes[..]);
                                let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                                (Elem::from(Concrete::from(U256::from(i))), (v, i))
                            })
                            .collect::<BTreeMap<_, _>>(),
                    ),
                    Concrete::Array(ref val) => Some(
                        val.iter()
                            .enumerate()
                            .map(|(i, v)| {
                                let t = Elem::Concrete(RangeConcrete::new(v.clone(), self.loc));
                                (Elem::from(Concrete::from(U256::from(i))), (t, i))
                            })
                            .collect::<BTreeMap<_, _>>(),
                    ),
                    Concrete::Bytes(size, val) => Some(
                        val.0
                            .iter()
                            .take(size as usize)
                            .enumerate()
                            .map(|(i, v)| {
                                let mut bytes = [0x00; 32];
                                bytes[0] = *v;
                                let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                                (Elem::from(Concrete::from(U256::from(i))), (v, i))
                            })
                            .collect::<BTreeMap<_, _>>(),
                    ),
                    _ => None,
                };
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    Elem::Concrete(other.clone()),
                    new?,
                    self.loc,
                )))
            }
        }
    }
}

impl RangeMemSet<Concrete, RangeDyn<Concrete>> for RangeConcrete<Concrete> {
    fn range_set_indices(&self, _range: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        todo!()
    }

    fn range_set_length(&self, _other: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete> for Elem<Concrete> {
    fn range_set_indices(&self, other: &Elem<Concrete>) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_set_indices(b),
            (Elem::ConcreteDyn(a), Elem::Concrete(b)) => a.range_set_indices(b),
            (Elem::Concrete(a), Elem::ConcreteDyn(b)) => a.range_set_indices(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => a.range_set_indices(b),
            _e => None,
        }
    }

    fn range_set_length(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => a.range_set_length(b),
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_set_length(b),
            (Elem::ConcreteDyn(a), _) => {
                let mut a = a.clone();
                a.len = Box::new(other.clone());
                Some(Elem::ConcreteDyn(a))
            }
            _e => None,
        }
    }
}

pub fn exec_set_length(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_max.range_set_length(rhs_max)
    } else {
        lhs_min.range_set_length(rhs_min)
    }
}

pub fn exec_set_indices(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    rhs: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    if maximize {
        if let Some(t) = lhs_max.range_set_indices(rhs_max) {
            Some(t)
        } else {
            let max = rhs.simplify_maximize(analyzer, arena).ok()?;
            lhs_max.range_set_indices(&max)
        }
    } else if let Some(t) = lhs_min.range_set_indices(rhs_min) {
        Some(t)
    } else {
        let min = rhs.simplify_minimize(analyzer, arena).ok()?;
        lhs_min.range_set_indices(&min)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use solang_parser::pt::Loc;

    #[test]
    fn concrete_set_len() {
        let x: RangeConcrete<Concrete> = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let new_len = rc_uint256(10);
        let result = x.range_set_length(&new_len).unwrap();
        assert_eq!(result.range_get_length().unwrap(), Elem::Concrete(new_len));
    }

    #[test]
    fn dyn_set_len() {
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let new_len = rc_uint256(10);
        let result = x.range_set_length(&new_len).unwrap();
        assert_eq!(result.range_get_length().unwrap(), Elem::Concrete(new_len));
    }

    #[test]
    fn dyn_set_ref_len() {
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let new_len = test_reference(0, U256::from(6), U256::from(10));
        let result = Elem::ConcreteDyn(x).range_set_length(&new_len).unwrap();
        assert_eq!(result.range_get_length().unwrap(), new_len);
    }

    #[test]
    fn concrete_concrete_set_indices() {
        let x = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o', b's']),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd']),
            Loc::Implicit,
        );

        let expected = RangeConcrete::new(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd', b's']),
            Loc::Implicit,
        );
        let result = x
            .range_set_indices(&y)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, expected.val);
    }

    #[test]
    fn dyn_concrete_index() {
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o', b's']),
            Loc::Implicit,
        )
        .unwrap();
        let y = RangeConcrete::new(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd']),
            Loc::Implicit,
        );

        let expected = RangeDyn::new_w_op_nums(
            rc_uint256(6).into(),
            vec![
                (
                    Elem::from(rc_uint256(0)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b'w'), Loc::Implicit)),
                        5usize,
                    ),
                ),
                (
                    Elem::from(rc_uint256(1)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b'o'), Loc::Implicit)),
                        6usize,
                    ),
                ),
                (
                    Elem::from(rc_uint256(2)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b'r'), Loc::Implicit)),
                        7usize,
                    ),
                ),
                (
                    Elem::from(rc_uint256(3)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b'l'), Loc::Implicit)),
                        8usize,
                    ),
                ),
                (
                    Elem::from(rc_uint256(4)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b'd'), Loc::Implicit)),
                        9usize,
                    ),
                ),
                (
                    Elem::from(rc_uint256(5)),
                    (
                        Elem::Concrete(RangeConcrete::new(Concrete::from(b's'), Loc::Implicit)),
                        5usize,
                    ),
                ),
            ]
            .into_iter()
            .collect::<BTreeMap<Elem<_>, (Elem<_>, usize)>>(),
            Loc::Implicit,
        );

        let result = x.range_set_indices(&y).unwrap();
        assert_eq!(result.dyn_map().unwrap(), &expected.val);
    }

    #[test]
    fn dyn_ref_set_indices() {
        let idx = test_reference(0, U256::ZERO, U256::from(2000));
        let rand: Elem<_> = rc_uint256(1337).into();
        let val: Elem<_> = rc_uint256(200).into();
        let x = RangeDyn::new_for_indices(vec![(rand.clone(), rand.clone())], Loc::Implicit);

        let y = RangeDyn::new_for_indices(vec![(idx.clone(), val.clone())], Loc::Implicit);

        let expected = Elem::ConcreteDyn(RangeDyn::new_for_indices(
            vec![(rand.clone(), rand), (idx.clone(), val)],
            Loc::Implicit,
        ));
        let result = x.range_set_indices(&y).unwrap();
        assert_eq!(result, expected);
    }

    fn test_reference(id: usize, min: U256, max: U256) -> Elem<Concrete> {
        let mut re = Reference::new(id.into());
        let mi = Box::new(Elem::Concrete(RangeConcrete::new(
            Concrete::from(min),
            Loc::Implicit,
        )));
        let ma = Box::new(Elem::Concrete(RangeConcrete::new(
            Concrete::from(max),
            Loc::Implicit,
        )));
        re.minimized = Some(MinMaxed::Minimized(mi.clone()));
        re.maximized = Some(MinMaxed::Maximized(ma.clone()));
        re.flattened_min = Some(mi);
        re.flattened_max = Some(ma);
        Elem::Reference(re)
    }
}
