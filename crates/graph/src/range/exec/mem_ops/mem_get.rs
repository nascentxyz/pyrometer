use crate::GraphBackend;
use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*},
};

use shared::RangeArena;

use alloy_primitives::U256;
use solang_parser::pt::Loc;

use std::collections::BTreeMap;

impl RangeMemLen<Concrete> for RangeDyn<Concrete> {
    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        Some(*self.len.clone())
    }
}

impl<Rhs: Into<Elem<Concrete>> + Clone> RangeMemGet<Concrete, Rhs> for RangeDyn<Concrete> {
    fn range_get_index(&self, index: &Rhs) -> Option<Elem<Concrete>> {
        self.val
            .get(&(index.clone().into()))
            .map(|(v, _)| v.clone())
    }
}

impl RangeMemGet<Concrete> for RangeConcrete<Concrete> {
    fn range_get_index(&self, index: &RangeConcrete<Concrete>) -> Option<Elem<Concrete>> {
        self.val.get_index(&index.val).map(Elem::from)
    }
}

impl RangeMemLen<Concrete> for RangeConcrete<Concrete> {
    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        Some(RangeConcrete::new(Concrete::from(self.val.maybe_array_size()?), self.loc).into())
    }
}

impl RangeMemLen<Concrete> for Elem<Concrete> {
    fn range_get_length(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => a.range_get_length(),
            Elem::ConcreteDyn(a) => Some(*a.len.clone()),
            _e => None,
        }
    }
}

impl RangeMemGet<Concrete, Elem<Concrete>> for Elem<Concrete> {
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

pub fn exec_slice(
    arr_min: &Elem<Concrete>,
    arr_max: &Elem<Concrete>,
    start: &Elem<Concrete>,
    end: &Elem<Concrete>,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Elem<Concrete> {
    let mut kvs = Default::default();
    // slices are exclusive
    let excl_end = end.clone() - Elem::from(Concrete::from(U256::from(1)));
    fn match_key(
        arr: &Elem<Concrete>,
        start_idx: &Elem<Concrete>,
        excl_end: &Elem<Concrete>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        kvs: &mut BTreeMap<Elem<Concrete>, Elem<Concrete>>,
    ) {
        match arr {
            Elem::Arena(_) => {
                let (d, idx) = arr.dearenaize(arena);
                match_key(&d, start_idx, excl_end, analyzer, arena, kvs);
                arr.rearenaize(d, idx, arena);
            }
            Elem::Reference(_) => {
                if let Ok(min) = arr.minimize(analyzer, arena) {
                    match_key(&min, start_idx, excl_end, analyzer, arena, kvs);
                }

                if let Ok(max) = arr.maximize(analyzer, arena) {
                    match_key(&max, start_idx, excl_end, analyzer, arena, kvs);
                }
            }
            Elem::ConcreteDyn(d) => {
                d.val.iter().for_each(|(k, (v, _op))| {
                    if let Ok(Some(true)) =
                        k.overlaps_dual(start_idx, excl_end, true, analyzer, arena)
                    {
                        let new_k = k.clone() - start_idx.clone();
                        kvs.insert(new_k, v.clone());
                    }
                });
            }
            Elem::Concrete(c) => {
                if let Some(size) = c.val.maybe_array_size() {
                    let min = U256::ZERO;
                    // Iterates through concrete indices to check if RHS contains the index
                    let mut curr = min;
                    while curr < size {
                        let as_rc = RangeConcrete::new(Concrete::from(curr), Loc::Implicit);
                        let as_elem = Elem::from(as_rc.clone());
                        if let Ok(Some(true)) =
                            as_elem.overlaps_dual(start_idx, excl_end, true, analyzer, arena)
                        {
                            if let Some(val) = c.range_get_index(&as_rc) {
                                let new_k = Elem::from(Concrete::from(curr)) - start_idx.clone();
                                kvs.insert(new_k, val.clone());
                            }
                        }
                        curr += U256::from(1);
                    }
                }
            }
            Elem::Expr(_) => {
                if let Ok(min) = arr.minimize(analyzer, arena) {
                    match_key(&min, start_idx, excl_end, analyzer, arena, kvs);
                }

                if let Ok(max) = arr.maximize(analyzer, arena) {
                    match_key(&max, start_idx, excl_end, analyzer, arena, kvs);
                }
            }
            _ => {}
        };
    }

    match_key(arr_min, start, &excl_end, analyzer, arena, &mut kvs);
    match_key(arr_max, start, &excl_end, analyzer, arena, &mut kvs);

    let len = Elem::Expr(RangeExpr::new(
        end.clone(),
        RangeOp::Sub(false),
        start.clone(),
    ));
    Elem::ConcreteDyn(RangeDyn::new(len, kvs, Loc::Implicit))
}

/// Executes the `get_length` operation given the minimum and maximum of an element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_get_length(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    if maximize {
        let new = lhs_max.clone();
        let new_max = new.simplify_maximize(analyzer, arena).ok()?;

        new_max.range_get_length()
    } else {
        let new_min = lhs_min.simplify_minimize(analyzer, arena).ok()?;

        new_min.range_get_length()
    }
}

/// Executes the `range_get_index` operation given the minimum and maximum of an element. It returns either the _minimum_ bound or _maximum_ bound
/// of the operation.
pub fn exec_get_index(
    lhs: &Elem<Concrete>,
    rhs: &Elem<Concrete>,
    maximize: bool,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    // for each key in LHS, check if it overlaps the RHS index range
    // e.g.:
    //  lhs: {
    //      [12, 100]: val,
    //      [220, 1000]: val,
    //  }
    //
    // if:
    //  rhs: [0, 2**224]
    //  all values would be added to candidates
    //
    // if:
    //  rhs: [0, 2]
    //  No values would be added to candidates
    //
    // if:
    //  rhs: [50, 50]
    //  the first value would be added to candidates

    let mut candidates = vec![];
    fn match_lhs(
        lhs: &Elem<Concrete>,
        rhs: &Elem<Concrete>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
        candidates: &mut Vec<Elem<Concrete>>,
    ) {
        match lhs {
            Elem::Arena(_) => {
                let (d, idx) = lhs.dearenaize(arena);
                match_lhs(&d, rhs, analyzer, arena, candidates);
                lhs.rearenaize(d, idx, arena);
            }
            Elem::Reference(_) => {
                if let Ok(min) = lhs.minimize(analyzer, arena) {
                    match_lhs(&min, rhs, analyzer, arena, candidates);
                }

                if let Ok(max) = lhs.maximize(analyzer, arena) {
                    match_lhs(&max, rhs, analyzer, arena, candidates);
                }
            }
            Elem::ConcreteDyn(d) => {
                d.val.iter().for_each(|(k, (v, _op))| {
                    if let Ok(Some(true)) = k.overlaps(rhs, true, analyzer, arena) {
                        candidates.push(v.clone())
                    }
                });
            }
            Elem::Concrete(c) => {
                if let Some(size) = c.val.maybe_array_size() {
                    let min = U256::ZERO;
                    // Iterates through concrete indices to check if RHS contains the index
                    let mut curr = min;
                    while curr < size {
                        let as_rc = RangeConcrete::new(Concrete::from(curr), Loc::Implicit);
                        let as_elem = Elem::from(as_rc.clone());
                        if let Ok(Some(true)) = as_elem.overlaps(rhs, true, analyzer, arena) {
                            if let Some(val) = c.range_get_index(&as_rc) {
                                candidates.push(val)
                            }
                        }
                        curr += U256::from(1);
                    }
                }
            }
            _ => {}
        };
    }

    match_lhs(lhs, rhs, analyzer, arena, &mut candidates);

    candidates = candidates
        .into_iter()
        .filter_map(|val| {
            if maximize {
                val.maximize(analyzer, arena).ok()
            } else {
                val.minimize(analyzer, arena).ok()
            }
        })
        .collect();

    // Sort the candidates
    candidates.sort_by(|a, b| match a.range_ord(b, arena) {
        Some(r) => r,
        _ => std::cmp::Ordering::Less,
    });

    if candidates.is_empty() {
        return Some(Elem::Null);
    }

    if maximize {
        Some(candidates.remove(candidates.len() - 1))
    } else {
        Some(candidates.remove(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DummyGraph;
    use pretty_assertions::assert_eq;

    #[test]
    fn concrete_len() {
        let x: RangeConcrete<Concrete> = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let expected = rc_uint256(5);
        let result = Elem::from(x)
            .range_get_length()
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, expected.val);
    }

    #[test]
    fn dyn_len() {
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let expected = rc_uint256(5);
        let result = x
            .range_get_length()
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, expected.val);
    }

    #[test]
    fn concrete_concrete_index() {
        let x = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let idx = rc_uint256(2);
        let result = x
            .range_get_index(&idx)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::from(b'l'));
    }

    #[test]
    fn dyn_concrete_index() {
        let x = RangeDyn::from_concrete(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        )
        .unwrap();
        let idx = rc_uint256(2);
        let result = x
            .range_get_index(&idx)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::from(b'l'));
    }

    #[test]
    fn dyn_ref_index() {
        let idx = Elem::Reference(Reference::new(1.into()));
        let rand: Elem<_> = rc_uint256(0).into();
        let val = rc_uint256(200).into();
        let x = RangeDyn::new_for_indices(
            vec![(rand.clone(), rand), (idx.clone(), val)],
            Loc::Implicit,
        );

        let result = x
            .range_get_index(&idx)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(200)));
    }

    #[test]
    fn exec_dyn_get_ref_idx_low() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let idx0 = test_reference(1, U256::from(12), U256::from(100));
        let idx1 = test_reference(2, U256::from(220), U256::from(1000));
        let val0 = rc_uint256(200).into();
        let val1 = rc_uint256(201).into();
        let x = RangeDyn::new_for_indices(vec![(idx0, val0), (idx1, val1)], Loc::Implicit);

        let get_idx = test_reference(3, U256::from(0), U256::from(12));

        let result = exec_get_index(&Elem::ConcreteDyn(x), &get_idx, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(200)));
    }

    #[test]
    fn exec_dyn_get_ref_idx_high() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let idx0 = test_reference(1, U256::from(12), U256::from(100));
        let idx1 = test_reference(2, U256::from(220), U256::from(1000));
        let val0 = rc_uint256(200).into();
        let val1 = rc_uint256(201).into();
        let x = RangeDyn::new_for_indices(vec![(idx0, val0), (idx1, val1)], Loc::Implicit);

        let get_idx = test_reference(3, U256::from(400), U256::from(400));

        let result = exec_get_index(&Elem::ConcreteDyn(x), &get_idx, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(201)));
    }

    #[test]
    fn exec_dyn_get_ref_idx_all() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let idx0 = test_reference(1, U256::from(12), U256::from(100));
        let idx1 = test_reference(2, U256::from(220), U256::from(1000));
        let val0 = rc_uint256(200).into();
        let val1 = rc_uint256(201).into();
        let x = RangeDyn::new_for_indices(vec![(idx0, val0), (idx1, val1)], Loc::Implicit);

        let get_idx = test_reference(3, U256::ZERO, U256::MAX);

        let result = exec_get_index(&Elem::ConcreteDyn(x), &get_idx, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(201)));
    }

    #[test]
    fn exec_dyn_get_ref_idx_null() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let idx0 = test_reference(1, U256::from(12), U256::from(100));
        let idx1 = test_reference(2, U256::from(220), U256::from(1000));
        let val0 = rc_uint256(200).into();
        let val1 = rc_uint256(201).into();
        let x = RangeDyn::new_for_indices(vec![(idx0, val0), (idx1, val1)], Loc::Implicit);

        let get_idx = test_reference(3, U256::from(0), U256::from(2));

        let result = exec_get_index(&Elem::ConcreteDyn(x), &get_idx, true, &g, &mut arena);
        assert_eq!(result.unwrap(), Elem::Null);
    }

    #[test]
    fn exec_concrete_get_ref_idx_low() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x: RangeConcrete<Concrete> = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let get_idx = test_reference(1, U256::ZERO, U256::from(2));

        let result = exec_get_index(&Elem::Concrete(x), &get_idx, true, &g, &mut arena)
            .unwrap()
            .maybe_concrete_value()
            .unwrap();
        assert_eq!(result.val, Concrete::from(b'l'));
    }

    #[test]
    fn exec_concrete_get_ref_idx_null() {
        let g = DummyGraph::default();
        let mut arena = Default::default();
        let x: RangeConcrete<Concrete> = RangeConcrete::new(
            Concrete::from(vec![b'h', b'e', b'l', b'l', b'o']),
            Loc::Implicit,
        );
        let get_idx = test_reference(1, U256::from(6), U256::from(8));

        let result = exec_get_index(&Elem::Concrete(x), &get_idx, true, &g, &mut arena);
        assert_eq!(result.unwrap(), Elem::Null);
    }

    fn test_reference(id: usize, min: U256, max: U256) -> Elem<Concrete> {
        let mut re = Reference::new(id.into());
        let mi = Box::new(Elem::Concrete(RangeConcrete::new(
            Concrete::from(min),
            Loc::Implicit,
        )));
        let ma = Box::new(Elem::Concrete(RangeConcrete::new(
            Concrete::from(max),
            Loc::Implicit,
        )));
        re.minimized = Some(MinMaxed::Minimized(mi.clone()));
        re.maximized = Some(MinMaxed::Maximized(ma.clone()));
        re.flattened_min = Some(mi);
        re.flattened_max = Some(ma);
        Elem::Reference(re)
    }
}
