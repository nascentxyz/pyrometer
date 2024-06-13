use crate::GraphBackend;
use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeElem},
};
use shared::RangeArena;

pub trait RangeArenaLike<T> {
    fn ranges(&self) -> &Vec<T>;
    fn ranges_mut(&mut self) -> &mut Vec<T>;
    fn idx_or_upsert(&mut self, elem: T, analyzer: &impl GraphBackend) -> usize;
    fn take_nonnull(&mut self, idx: usize) -> Option<T>;
    fn idx(&self, elem: &T) -> Option<usize>;
}

impl RangeArenaLike<Elem<Concrete>> for RangeArena<Elem<Concrete>> {
    fn idx_or_upsert(&mut self, elem: Elem<Concrete>, analyzer: &impl GraphBackend) -> usize {
        if let Elem::Arena(idx) = elem {
            return idx;
        }

        // if let Elem::Reference(..) = elem {
        //     panic!("here");
        // }

        if let Some(idx) = self.idx(&elem) {
            let Some(existing) = self.take_nonnull(idx) else {
                self.ranges_mut()[idx] = elem;
                return idx;
            };

            let (min_cached, max_cached) = existing.is_min_max_cached(analyzer, self);
            let mut existing_count = 0;
            if min_cached {
                existing_count += 1;
            }
            if max_cached {
                existing_count += 1;
            }
            if existing.is_flatten_cached(analyzer, self) {
                existing_count += 1;
            }

            let (min_cached, max_cached) = elem.is_min_max_cached(analyzer, self);
            let mut new_count = 0;
            if min_cached {
                new_count += 1;
            }
            if max_cached {
                new_count += 1;
            }
            if elem.is_flatten_cached(analyzer, self) {
                new_count += 1;
            }

            if new_count >= existing_count {
                self.ranges_mut()[idx] = elem;
            } else {
                self.ranges_mut()[idx] = existing;
            }

            idx
        } else {
            let idx = self.ranges.len();
            self.ranges.push(elem.clone());
            self.map.insert(elem, idx);
            idx
        }
    }

    fn ranges(&self) -> &Vec<Elem<Concrete>> {
        &self.ranges
    }
    fn ranges_mut(&mut self) -> &mut Vec<Elem<Concrete>> {
        &mut self.ranges
    }

    fn take_nonnull(&mut self, idx: usize) -> Option<Elem<Concrete>> {
        if let Some(t) = self.ranges.get_mut(idx) {
            match t {
                Elem::Null => None,
                _ => Some(std::mem::take(t)),
            }
        } else {
            None
        }
    }

    fn idx(&self, elem: &Elem<Concrete>) -> Option<usize> {
        if let Elem::Arena(idx) = elem {
            Some(*idx)
        } else {
            self.map.get(elem).copied()
        }
    }
}
