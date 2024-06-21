use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use shared::RangeArena;

impl RangeMax<Concrete> for RangeConcrete<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.max(rhs_val);
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, _))
                | (Concrete::Int(lhs_size, _), Concrete::Uint(_, val)) => {
                    let val = Concrete::Uint(*lhs_size, *val);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let val = Concrete::Int(*lhs_size, *l.max(r));
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeMax<Concrete> for Elem<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_max(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => match a.op_num.cmp(&b.op_num) {
                std::cmp::Ordering::Greater => Some(self.clone()),
                std::cmp::Ordering::Less => Some(other.clone()),
                _ => None,
            },
            (_, Elem::Null) => Some(self.clone()),
            (Elem::Null, _) => Some(other.clone()),
            _ => None,
        }
    }
}

/// Executes the maximum given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_max(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    _analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_max(rhs_min),
        lhs_min.range_max(rhs_max),
        lhs_max.range_max(rhs_min),
        lhs_max.range_max(rhs_max),
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
