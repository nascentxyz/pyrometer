use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*}
};

use ethers_core::types::{H256, U256};

use std::collections::BTreeMap;

impl RangeMemSet<Concrete> for RangeDyn<Concrete> {
    fn range_set_indices(&self, range: &Self) -> Option<Elem<Concrete>> {
        let mut new_val = self.val.clone();
        let mut op_num = self.op_num;
        range.val.iter().for_each(|(k, (v, _))| {
            op_num += 1;
            new_val.insert(k.clone(), (v.clone(), op_num));
        });

        Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
            *self.len.clone(),
            new_val,
            range.loc,
        )))
    }

    fn range_get_index(&self, _index: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_set_length(&self, _other: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_set_indices(&self, range: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        match (range.val.clone(), self.val.iter().take(1).next()) {
            (
                Concrete::DynBytes(val),
                Some((
                    _,
                    (Elem::Concrete(RangeConcrete {
                        val: Concrete::Bytes(..),
                        ..
                    }), _),
                )),
            )
            | (Concrete::DynBytes(val), None) => {
                let mut existing = self.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (Elem::from(Concrete::from(U256::from(i))), (v, self.op_num + i))
                    })
                    .collect::<BTreeMap<_, _>>();
                existing.extend(new);
                Some(Elem::ConcreteDyn(RangeDyn::new_w_op_nums(
                    *self.len.clone(),
                    existing,
                    range.loc,
                )))
            }
            (
                Concrete::String(val),
                Some((
                    _,
                    (Elem::Concrete(RangeConcrete {
                        val: Concrete::String(..),
                        ..
                    }), _),
                )),
            )
            | (Concrete::String(val), None) => {
                let mut existing = self.val.clone();
                let new = val
                    .chars()
                    .enumerate()
                    .map(|(i, v)| {
                        let mut bytes = [0x00; 32];
                        v.encode_utf8(&mut bytes[..]);
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                        (Elem::from(Concrete::from(U256::from(i))), (v, i + self.op_num))
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

    fn range_get_index(&self, _index: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_set_length(&self, _other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete> for RangeConcrete<Concrete> {
    fn range_set_indices(&self, range: &Self) -> Option<Elem<Concrete>> {
        let mut new_val = self.val.clone();
        new_val.set_indices(&range.val);
        Some(Elem::Concrete(RangeConcrete {
            val: new_val,
            loc: range.loc,
        }))
    }

    fn range_get_index(&self, index: &Self) -> Option<Elem<Concrete>> {
        self.val.get_index(&index.val).map(Elem::from)
    }


    fn range_set_length(&self, _other: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete, RangeDyn<Concrete>> for RangeConcrete<Concrete> {
    fn range_set_indices(&self, _range: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        todo!()
    }

    fn range_get_index(&self, _range: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }


    fn range_set_length(&self, _other: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete> for Elem<Concrete> {
    fn range_set_indices(&self, other: &Elem<Concrete>) -> Option<Elem<Concrete>> {
        println!("setting indices: {self}, {other}");
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
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => {
                let mut a = a.clone();
                a.len = b.len.clone();
                Some(Elem::ConcreteDyn(a.clone()))
            },
            (a @ Elem::Concrete(_), _b @ Elem::Concrete(_)) => {
                Some(a.clone())
            },
            (Elem::ConcreteDyn(a), _) => {
                let mut a = a.clone();
                a.len = Box::new(other.clone());
                Some(Elem::ConcreteDyn(a.clone()))
            },
            _e => None,
        }
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => Some(Elem::from(Concrete::from(a.val.maybe_array_size()?))),
            Elem::ConcreteDyn(a) => Some(*a.len.clone()),
            _e => None,
        }
    }

    fn range_get_index(&self, index: &Elem<Concrete>) -> Option<Elem<Concrete>> {
        match (self, index) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_get_index(b),
            (Elem::ConcreteDyn(a), idx @ Elem::Concrete(_)) => {
                if let Some((val, _)) = a.val.get(idx).cloned() {
                    Some(val)
                } else {
                    None
                }
            },
            (Elem::ConcreteDyn(a), idx @ Elem::Reference(_)) => {
                if let Some((val, _)) = a.val.get(idx).cloned() {
                    Some(val)
                } else {
                    None
                }
            }
            _e => None,
        }
    }
}
