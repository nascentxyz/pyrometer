use crate::GraphBackend;
use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*},
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

    fn range_set_length(&self, _other: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_set_indices(&self, range: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        match (
            range.val.clone(),
            self.val.values().take(1).next().and_then(|(a, _)| Some(a)),
        ) {
            (Concrete::DynBytes(val), s) if s.is_none() || s.unwrap().is_bytes() => {
                let mut existing = self.val.clone();
                let new = val
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let mut bytes = [0x00; 32];
                        bytes[0] = *v;
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
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
                        let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
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

    fn range_set_length(&self, _other: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemSet<Concrete> for RangeConcrete<Concrete> {
    fn range_set_indices(&self, range: &Self) -> Option<Elem<Concrete>> {
        let mut new_val = self.val.clone();
        new_val.set_indices(&range.val);
        Some(Elem::Concrete(RangeConcrete::new(new_val, range.loc)))
    }

    fn range_set_length(&self, _other: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
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
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => {
                let mut a = a.clone();
                a.len.clone_from(&b.len);
                Some(Elem::ConcreteDyn(a.clone()))
            }
            (a @ Elem::Concrete(_), _b @ Elem::Concrete(_)) => Some(a.clone()),
            (Elem::ConcreteDyn(a), _) => {
                let mut a = a.clone();
                a.len = Box::new(other.clone());
                Some(Elem::ConcreteDyn(a.clone()))
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
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_max.range_set_length(&rhs_max)
    } else {
        lhs_min.range_set_length(&rhs_min)
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
) -> Option<Elem<Concrete>> {
    if maximize {
        if let Some(t) = lhs_max.range_set_indices(&rhs_max) {
            Some(t)
        } else {
            let max = rhs.simplify_maximize(analyzer).ok()?;
            lhs_max.range_set_indices(&max)
        }
    } else {
        if let Some(t) = lhs_min.range_set_indices(&rhs_min) {
            Some(t)
        } else {
            let min = rhs.simplify_minimize(analyzer).ok()?;
            lhs_min.range_set_indices(&min)
        }
    }
}
