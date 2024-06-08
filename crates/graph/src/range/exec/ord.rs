use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use crate::GraphBackend;

use solang_parser::pt::Loc;

impl RangeOrd<Concrete> for RangeConcrete<Concrete> {
    fn range_ord_eq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                let rc = RangeConcrete::new(Concrete::Bool(lhs_val == rhs_val), self.loc);
                Some(rc.into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(false), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l == r), self.loc).into())
                }
                _ => None,
            },
        }
    }

    fn range_neq(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(RangeConcrete::new(Concrete::Bool(lhs_val != rhs_val), self.loc).into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_, _), Concrete::Int(_, _))
                | (Concrete::Int(_, _), Concrete::Uint(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(true), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l != r), self.loc).into())
                }
                _ => None,
            },
        }
    }

    fn range_gt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(RangeConcrete::new(Concrete::Bool(lhs_val > rhs_val), self.loc).into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(true), self.loc).into())
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(RangeConcrete::new(Concrete::Bool(false), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l > r), self.loc).into())
                }
                _ => None,
            },
        }
    }

    fn range_lt(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(RangeConcrete::new(Concrete::Bool(lhs_val < rhs_val), self.loc).into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(false), self.loc).into())
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(RangeConcrete::new(Concrete::Bool(true), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l < r), self.loc).into())
                }
                _ => None,
            },
        }
    }

    fn range_gte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(RangeConcrete::new(Concrete::Bool(lhs_val >= rhs_val), self.loc).into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(true), self.loc).into())
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(RangeConcrete::new(Concrete::Bool(false), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l >= r), self.loc).into())
                }
                _ => None,
            },
        }
    }

    fn range_lte(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(lhs_val), Some(rhs_val)) => {
                Some(RangeConcrete::new(Concrete::Bool(lhs_val <= rhs_val), self.loc).into())
            }
            _ => match (&self.val, &other.val) {
                (Concrete::Uint(_lhs_size, _val), Concrete::Int(_, _)) => {
                    Some(RangeConcrete::new(Concrete::Bool(false), self.loc).into())
                }
                (Concrete::Int(_lhs_size, _), Concrete::Uint(_, _val)) => {
                    Some(RangeConcrete::new(Concrete::Bool(true), self.loc).into())
                }
                (Concrete::Int(_lhs_size, l), Concrete::Int(_rhs_size, r)) => {
                    Some(RangeConcrete::new(Concrete::Bool(l <= r), self.loc).into())
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

/// Executes the `greater than` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_gt(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_max.range_gt(rhs_min)
    } else {
        lhs_min.range_gt(rhs_max)
    }
}

/// Executes the `less than` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_lt(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_min.range_lt(rhs_max)
    } else {
        lhs_max.range_lt(rhs_min)
    }
}

/// Executes the `greater than or equal` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_gte(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_max.range_gte(rhs_min)
    } else {
        lhs_min.range_gte(rhs_max)
    }
}

/// Executes the `less than or equal` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_lte(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        lhs_min.range_lte(rhs_max)
    } else {
        lhs_max.range_lte(rhs_min)
    }
}

/// Executes the `equal` operation or `not equal` operation given the minimum and maximum of each element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_eq_neq(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    eq: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    // prevent trying to eval when we have dependents
    if !lhs_min.dependent_on(analyzer).is_empty()
        || !lhs_max.dependent_on(analyzer).is_empty()
        || !rhs_min.dependent_on(analyzer).is_empty()
        || !rhs_max.dependent_on(analyzer).is_empty()
    {
        return None;
    }

    let loc = if let Some(c) = lhs_min.maybe_concrete() {
        c.loc
    } else if let Some(c) = lhs_max.maybe_concrete() {
        c.loc
    } else if let Some(c) = rhs_min.maybe_concrete() {
        c.loc
    } else if let Some(c) = rhs_max.maybe_concrete() {
        c.loc
    } else {
        Loc::Implicit
    };

    // We want to prove that there exists some values for LHS and RHS that are equal
    // We do this for equality maximization and inequality minimization
    let overlap_test = eq && maximize || !eq && !maximize;

    if overlap_test {
        // check for any overlap
        //
        // Check if lhs max > rhs min
        // LHS: <--?---| max
        // RHS:  min |----?---->
        let lhs_max_rhs_min_ord = lhs_max.range_ord(rhs_min, analyzer);

        // Check if lhs min < rhs max
        // LHS: min |----?---->
        // RHS: <--?---| max
        let lhs_min_rhs_max_ord = lhs_min.range_ord(rhs_max, analyzer);

        // if lhs max is less than the rhs min, it has to be false
        if matches!(lhs_max_rhs_min_ord, Some(std::cmp::Ordering::Less)) {
            return Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(!eq),
                loc,
            }));
        }

        // if lhs min is greater than the rhs max, it has to be false
        if matches!(lhs_min_rhs_max_ord, Some(std::cmp::Ordering::Greater)) {
            return Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(!eq),
                loc,
            }));
        }

        // lhs_max >= rhs_min
        // lhs_min <= rhs_max
        Some(Elem::Concrete(RangeConcrete {
            val: Concrete::Bool(eq),
            loc,
        }))
    } else {
        // We want to check that there is *some* case in which they can be *not* equal.
        // This only occurs when both sides are constant and equal
        match (
            // check if lhs is constant
            lhs_min.range_ord(lhs_max, analyzer),
            // check if rhs is constant
            rhs_min.range_ord(rhs_max, analyzer),
            // check if lhs is equal to rhs
            lhs_min.range_ord(rhs_min, analyzer),
        ) {
            // LHS & RHS are constant and equal
            (
                Some(std::cmp::Ordering::Equal),
                Some(std::cmp::Ordering::Equal),
                Some(std::cmp::Ordering::Equal),
            ) => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(eq),
                loc,
            })),
            // LHS or RHS is not constant or they are constant and unequal
            _ => Some(Elem::Concrete(RangeConcrete {
                val: Concrete::Bool(!eq),
                loc,
            })),
        }
    }
}
