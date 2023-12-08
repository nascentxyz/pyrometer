use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};

impl RangeUnary<Concrete> for RangeConcrete<Concrete> {
    fn range_not(&self) -> Option<Elem<Concrete>> {
        match self.val {
            Concrete::Bool(b) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(!b),
                loc: self.loc,
            })),
            _ => None,
        }
    }

    fn range_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(*a && *b),
                loc: self.loc,
            })),
            _ => None,
        }
    }

    fn range_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Bool(a), Concrete::Bool(b)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(*a || *b),
                loc: self.loc,
            })),
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