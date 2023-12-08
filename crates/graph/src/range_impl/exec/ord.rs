impl RangeOrd<Concrete> for RangeConcrete<Concrete> {
    fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val == rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l == r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val != rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l != r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val > rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l > r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val < rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l < r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val >= rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l >= r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(lhs_val <= rhs_val),
                loc: self.loc,
            })),
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc: self.loc,
                    }))
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(l <= r),
                        loc: self.loc,
                    }))
                }
                _ => None,
            },
        }
    }
}

impl RangeOrd<Concrete> for Elem<Concrete> {
    fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_ord_eq(b),
            _ => None,
        }
    }
    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_neq(b),
            _ => None,
        }
    }
    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_gt(b),
            _ => None,
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_lt(b),
            _ => None,
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_gte(b),
            _ => None,
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_lte(b),
            _ => None,
        }
    }
}