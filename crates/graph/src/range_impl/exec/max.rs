impl RangeMax<Concrete> for RangeConcrete<Concrete> {
    fn range_max(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: self.val.u256_as_original(lhs_val.max(rhs_val)),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(lhs_size, val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(*lhs_size, *val),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, _), Concrete::Uint(_, val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Uint(*lhs_size, *val),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Int(*lhs_size, *l.max(r)),
                        loc: self.loc,
                    }))
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
            _ => None,
        }
    }
}