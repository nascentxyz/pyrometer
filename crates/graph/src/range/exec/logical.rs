use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

impl RangeUnary<Concrete> for RangeConcrete<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self.val {
            Concrete::Bool(b) => Some(RangeConcrete::new(Concrete::Bool(!b), self.loc).into()),
            _ => None,
        }
    }

    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => {
                Some(RangeConcrete::new(Concrete::Bool(*a && *b), self.loc).into())
            }
            _ => None,
        }
    }

    fn range_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => {
                Some(RangeConcrete::new(Concrete::Bool(*a || *b), self.loc).into())
            }
            _ => None,
        }
    }
}

impl RangeUnary<Concrete> for Elem<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => a.range_not(),
            _ => None,
        }
    }
    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_and(b),
            _ => None,
        }
    }
    fn range_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_or(b),
            _ => None,
        }
    }
}

pub fn exec_and(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_and(&rhs_min),
        lhs_min.range_and(&rhs_max),
        lhs_max.range_and(&rhs_min),
        lhs_max.range_and(&rhs_max),
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

pub fn exec_or(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    let candidates = vec![
        lhs_min.range_or(&rhs_min),
        lhs_min.range_or(&rhs_max),
        lhs_max.range_or(&rhs_min),
        lhs_max.range_or(&rhs_max),
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

pub fn exec_not(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    assert!(matches!(rhs_min, Elem::Null) && matches!(rhs_max, Elem::Null));
    let candidates = vec![lhs_min.range_not(), lhs_max.range_not()];
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
