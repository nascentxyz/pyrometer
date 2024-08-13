use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

use alloy_primitives::{B256, U256};
use std::collections::BTreeMap;

impl RangeConcat<Concrete> for RangeConcrete<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        Some(Elem::Concrete(RangeConcrete::new(
            self.val.clone().concat(&other.val)?,
            self.loc,
        )))
    }
}

impl RangeConcat<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_concat(&self, other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        let inner = self.val.values().take(1).next().map(|(a, _)| a);
        match (other.val.clone(), inner) {
            (Concrete::DynBytes(val), inner) if inner.is_none() || inner.unwrap().is_bytes() => {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let idx = *last.clone() + idx;
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                        (idx, (v, self.op_num + i + 1))
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    (*self.len).clone() + Elem::from(Concrete::from(U256::from(val.len()))),
                    existing,
                    other.loc,
                )))
            }
            (Concrete::String(val), inner)
                if inner.is_none() || inner.unwrap().is_string() || inner.unwrap().is_bytes() =>
            {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let new = val
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let idx = Elem::from(Concrete::from(U256::from(i)));
                        let idx = *last.clone() + idx;
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, B256::from(bytes)));
                        (idx, (v, self.op_num + i + 1))
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    (*self.len).clone() + Elem::from(Concrete::from(U256::from(val.len()))),
                    existing,
                    other.loc,
                )))
            }
            e => {
                debug_assert!(false, "was not concattable type: {e:#?}");
                None
            }
        }
    }
}

impl RangeConcat<Concrete, RangeDyn<Concrete>> for RangeDyn<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        let val = self.val.values().take(1).next().map(|(a, _)| a);
        let o_val = other.val.values().take(1).next().map(|(a, _)| a);
        match (val, o_val) {
            (Some(v), Some(o)) if v.is_bytes() && o.is_bytes() => {
                let last = self.len.clone();
                let mut existing = self.val.clone();
                let other_vals = other
                    .val
                    .clone()
                    .into_iter()
                    .enumerate()
                    .map(|(i, (key, (v, _op)))| (key + *last.clone(), (v, self.op_num + i + 1)))
                    .collect::<BTreeMap<_, _>>();

                existing.extend(other_vals);

                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    *self.len.clone() + *other.len.clone(),
                    existing,
                    other.loc,
                )))
            }
            (Some(l @ Elem::Reference(_)), None) => Some(l.clone()),
            (None, Some(r @ Elem::Reference(_))) => Some(r.clone()),
            (None, None) => Some(Elem::ConcreteDyn(self.clone())),
            _e => None,
        }
    }
}

impl RangeConcat<Concrete> for Elem<Concrete> {
    fn range_concat(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_concat(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => a.range_concat(b),
            (Elem::Concrete(c), Elem::ConcreteDyn(d))
            | (Elem::ConcreteDyn(d), Elem::Concrete(c)) => d.range_concat(c),
            _e => None,
        }
    }
}

/// Executes a concatenation of bytes.
pub fn exec_concat(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    // TODO: improve with smarter stuff
    let candidates = vec![
        lhs_min.range_concat(rhs_min),
        lhs_min.range_concat(rhs_max),
        lhs_max.range_concat(rhs_min),
        lhs_max.range_concat(rhs_max),
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
    use crate::DummyGraph;
    use pretty_assertions::assert_eq;
    use solang_parser::pt::Loc;

    #[test]
    fn concrete_concrete_bytes() {
        let x = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd']),
            Loc::Implicit,
        );
        let expected = Concrete::from(vec![
            b'h', b'e', b'l', b'l', b'o', b'w', b'o', b'r', b'l', b'd',
        ]);
        let result = x.range_concat(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, expected);
    }

    #[test]
    fn concrete_concrete_bytes_str_fail() {
        let x = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::from("world"), Loc::Implicit);
        assert!(x.range_concat(&y).is_none());
    }

    #[test]
    fn concrete_concrete_bytes_none() {
        let x = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let y = RangeConcrete::new(Concrete::DynBytes(vec![]), Loc::Implicit);
        let result = x.range_concat(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, x.val);
    }

    #[test]
    fn concrete_concrete_str() {
        let x = RangeConcrete::new(Concrete::from("hello"), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from("world"), Loc::Implicit);
        let expected = Concrete::from("helloworld");
        let result = x.range_concat(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, expected);
    }

    #[test]
    fn concrete_concrete_str_bytes_fail() {
        let x = RangeConcrete::new(Concrete::from("world"), Loc::Implicit);
        let y = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        assert!(x.range_concat(&y).is_none());
    }

    #[test]
    fn concrete_concrete_str_none() {
        let x = RangeConcrete::new(Concrete::from("hello"), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(""), Loc::Implicit);
        let result = x.range_concat(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, x.val);
    }

    #[test]
    fn dyn_concrete_bytes() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let y = RangeConcrete::new(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd']),
            Loc::Implicit,
        );
        let expected: Elem<_> = Elem::ConcreteDyn(
            RangeDyn::from_concrete(
                Concrete::from(vec![
                    b'h', b'e', b'l', b'l', b'o', b'w', b'o', b'r', b'l', b'd',
                ]),
                Loc::Implicit,
            )
            .unwrap(),
        );
        let result = x
            .range_concat(&y)
            .unwrap()
            .maximize(&g, &mut arena)
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn dyn_dyn_bytes() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let y = RangeDyn::from_concrete(
            Concrete::from(vec![b'w', b'o', b'r', b'l', b'd']),
            Loc::Implicit,
        )
        .unwrap();
        let expected: Elem<_> = Elem::ConcreteDyn(
            RangeDyn::from_concrete(
                Concrete::from(vec![
                    b'h', b'e', b'l', b'l', b'o', b'w', b'o', b'r', b'l', b'd',
                ]),
                Loc::Implicit,
            )
            .unwrap(),
        );
        let result = x
            .range_concat(&y)
            .unwrap()
            .maximize(&g, &mut arena)
            .unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn dyn_concrete_str() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x = RangeDyn::from_concrete(Concrete::from("hello"), Loc::Implicit).unwrap();
        let y = RangeConcrete::new(Concrete::from("world"), Loc::Implicit);
        let expected: Elem<_> = Elem::ConcreteDyn(
            RangeDyn::from_concrete(Concrete::from("helloworld"), Loc::Implicit).unwrap(),
        );
        let result = x.range_concat(&y).unwrap();
        let result = result.maximize(&g, &mut arena).unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn dyn_dyn_str() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x = RangeDyn::from_concrete(Concrete::from("hello"), Loc::Implicit).unwrap();
        let y = RangeDyn::from_concrete(Concrete::from("world"), Loc::Implicit).unwrap();
        let expected: Elem<_> = Elem::ConcreteDyn(
            RangeDyn::from_concrete(Concrete::from("helloworld"), Loc::Implicit).unwrap(),
        );
        let result = x
            .range_concat(&y)
            .unwrap()
            .maximize(&g, &mut arena)
            .unwrap();
        assert_eq!(result, expected);
    }
}
