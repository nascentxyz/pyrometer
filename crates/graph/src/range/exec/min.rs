use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

impl RangeMin<Concrete> for RangeConcrete<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let op_res = lhs_val.min(rhs_val);
                let val = self.val.u256_as_original(op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, _), Concrete::Int(_, neg_v))
                | (Concrete::Int(lhs_size, neg_v), Concrete::Uint(_, _)) => {
                    let val = Concrete::Int(*lhs_size, *neg_v);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    let val = Concrete::Int(*lhs_size, *l.min(r));
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                }
                _ => None,
            },
        }
    }
}

impl RangeMin<Concrete> for Elem<Concrete> {
    fn range_min(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_min(b),
            (Elem::ConcreteDyn(a), Elem::ConcreteDyn(b)) => match a.op_num.cmp(&b.op_num) {
                std::cmp::Ordering::Greater => Some(self.clone()),
                std::cmp::Ordering::Less => Some(other.clone()),
                _ => None,
            },
            (c @ Elem::Concrete(_), Elem::ConcreteDyn(b))
            | (Elem::ConcreteDyn(b), c @ Elem::Concrete(_)) => {
                if b.op_num == 0 {
                    Some(c.clone())
                } else {
                    None
                }
            }
            (_, Elem::Null) => Some(self.clone()),
            (Elem::Null, _) => Some(other.clone()),
            _ => None,
        }
    }
}

/// Executes the minimum given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_min(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_min(rhs_min),
        lhs_min.range_min(rhs_max),
        lhs_max.range_min(rhs_min),
        lhs_max.range_min(rhs_max),
    ];
    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
    candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
