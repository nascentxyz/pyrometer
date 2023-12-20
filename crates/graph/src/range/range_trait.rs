use crate::{range::elem::RangeElem, GraphBackend};
use shared::NodeIdx;
use std::borrow::Cow;

pub trait Range<T: Ord> {
    type GraphError;
    type ElemTy: RangeElem<T> + Clone;
    /// Evaluate both the minimum and the maximum - cache along the way
    fn cache_eval(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), Self::GraphError>;
    /// Evaluate the range minimum
    fn evaled_range_min(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Self::ElemTy, Self::GraphError>;
    /// Evaluate the range maximum
    fn evaled_range_max(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Self::ElemTy, Self::GraphError>;
    /// Simplify the minimum, leaving references in place
    fn simplified_range_min(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Self::ElemTy, Self::GraphError>;
    /// Simplify the maximum, leaving references in place
    fn simplified_range_max(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Self::ElemTy, Self::GraphError>;
    /// Return the range minimum
    fn range_min(&self) -> std::borrow::Cow<'_, Self::ElemTy>;
    /// Return the range maximum
    fn range_max(&self) -> std::borrow::Cow<'_, Self::ElemTy>;
    /// Uncache the range minimum
    fn uncache_range_min(&mut self) {
        self.range_min_mut().uncache();
    }
    /// Uncache the range maximum
    fn uncache_range_max(&mut self) {
        self.range_max_mut().uncache();
    }
    /// Get a mutable reference to the minimum
    fn range_min_mut(&mut self) -> &mut Self::ElemTy;
    /// Get a mutable reference to the maximum
    fn range_max_mut(&mut self) -> &mut Self::ElemTy;
    /// Get the range exclusions
    fn range_exclusions(&self) -> Vec<Self::ElemTy>
    where
        Self: std::marker::Sized;
    /// Set the range minimum
    fn set_range_min(&mut self, new: Self::ElemTy);
    /// Set the range maximum
    fn set_range_max(&mut self, new: Self::ElemTy);
    /// Set the range exclusions
    fn set_range_exclusions(&mut self, new: Vec<Self::ElemTy>)
    where
        Self: std::marker::Sized;
    /// Add an exclusion value to the range
    fn add_range_exclusion(&mut self, new: Self::ElemTy)
    where
        Self: std::marker::Sized;
    /// Replace a potential recursion causing node index with a new index
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx, analyzer: &impl GraphBackend);
    /// Replace a potential recursion causing node index with a new index
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx, analyzer: &impl GraphBackend);
    /// Cache the flattened range
    fn cache_flatten(&mut self, analyzer: &impl GraphBackend) -> Result<(), Self::GraphError>;
    /// Produce a flattened range or use the cached flattened range
    fn flattened_range<'a>(
        &'a self,
        analyzer: &impl GraphBackend,
    ) -> Result<Cow<'a, Self>, Self::GraphError>
    where
        Self: Sized + Clone;
}

pub trait RangeEval<E: Ord, T: RangeElem<E>>: Range<E, ElemTy = T> {
    fn sat(&self, analyzer: &impl GraphBackend) -> bool;
    fn unsat(&self, analyzer: &impl GraphBackend) -> bool {
        !self.sat(analyzer)
    }
    fn contains(&self, other: &Self, analyzer: &impl GraphBackend) -> bool;
    fn contains_elem(&self, other: &T, analyzer: &impl GraphBackend) -> bool;
    fn overlaps(&self, other: &Self, analyzer: &impl GraphBackend) -> bool;
}
