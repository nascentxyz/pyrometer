use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*},
};
use crate::{GraphBackend, GraphError};

impl RangeMemGet<Concrete> for RangeDyn<Concrete> {
    fn range_get_index(&self, _index: &Self) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemGet<Concrete, RangeConcrete<Concrete>> for RangeDyn<Concrete> {
    fn range_get_index(&self, _index: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemGet<Concrete, RangeDyn<Concrete>> for RangeConcrete<Concrete> {
    fn range_get_index(&self, _range: &RangeDyn<Concrete>) -> Option<Elem<Concrete>> {
        unreachable!()
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemGet<Concrete> for RangeConcrete<Concrete> {
    fn range_get_index(&self, index: &Self) -> Option<Elem<Concrete>> {
        self.val.get_index(&index.val).map(Elem::from)
    }

    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        unreachable!()
    }
}

impl RangeMemGet<Concrete> for Elem<Concrete> {
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
            }
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

/// Executes the `get_length` operation given the minimum and maximum of an element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_get_length(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    if maximize {
        let new = lhs_max.clone();
        let new_max = new.simplify_maximize(analyzer).ok()?;

        new_max.range_get_length()
    } else {
        let new_min = lhs_min.simplify_minimize(analyzer).ok()?;

        new_min.range_get_length()
    }
}

/// Executes the `range_get_index` operation given the minimum and maximum of an element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_get_index(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    rhs_min: &Elem<Concrete>,
    rhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
) -> Option<Elem<Concrete>> {
    if maximize {
        fn match_ty_max(
            lhs_max: &Elem<Concrete>,
            rhs_min: &Elem<Concrete>,
            rhs_max: &Elem<Concrete>,
            analyzer: &impl GraphBackend,
        ) -> Result<Elem<Concrete>, GraphError> {
            match lhs_max {
                Elem::ConcreteDyn(RangeDyn { val, .. }) => Ok(val
                    .iter()
                    .try_fold(None, |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                        if matches!(
                            key.overlaps_dual(rhs_min, rhs_max, true, analyzer)?,
                            Some(true)
                        ) {
                            if acc.is_none()
                                || matches!(
                                    acc.clone().unwrap().range_ord(val, analyzer),
                                    Some(std::cmp::Ordering::Greater)
                                )
                            {
                                acc = Some(val.clone());
                                Ok(acc)
                            } else {
                                Ok(acc)
                            }
                        } else {
                            Ok(acc)
                        }
                    })?
                    .unwrap_or_else(|| Elem::Null)),
                Elem::Reference(_) => {
                    let new_max = lhs_max.simplify_maximize(analyzer)?;
                    if &new_max == lhs_max {
                        Ok(Elem::Null)
                    } else {
                        match_ty_max(&new_max, rhs_min, rhs_max, analyzer)
                    }
                }
                _ => Ok(Elem::Null),
            }
        }
        match_ty_max(lhs_max, rhs_min, rhs_max, analyzer).ok()
    } else {
        fn match_ty_min(
            lhs_min: &Elem<Concrete>,
            rhs_min: &Elem<Concrete>,
            rhs_max: &Elem<Concrete>,
            analyzer: &impl GraphBackend,
        ) -> Result<Elem<Concrete>, GraphError> {
            match lhs_min {
                Elem::ConcreteDyn(RangeDyn { val, .. }) => Ok(val
                    .iter()
                    .try_fold(None, |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                        if matches!(
                            key.overlaps_dual(rhs_min, rhs_max, true, analyzer)?,
                            Some(true)
                        ) {
                            if acc.is_none()
                                || matches!(
                                    acc.clone().unwrap().range_ord(val, analyzer),
                                    Some(std::cmp::Ordering::Less)
                                )
                            {
                                acc = Some(val.clone());
                                Ok(acc)
                            } else {
                                Ok(acc)
                            }
                        } else {
                            Ok(acc)
                        }
                    })?
                    .unwrap_or_else(|| Elem::Null)),
                Elem::Reference(ref _r) => {
                    let new_min = lhs_min.simplify_minimize(analyzer)?;
                    if &new_min == lhs_min {
                        Ok(Elem::Null)
                    } else {
                        match_ty_min(&new_min, rhs_min, rhs_max, analyzer)
                    }
                }
                _ => Ok(Elem::Null),
            }
        }
        match_ty_min(lhs_min, rhs_min, rhs_max, analyzer).ok()
    }
}
