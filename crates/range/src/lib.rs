mod elem;
mod exec;
mod solc_range;
mod range_string;

pub use elem::*;
pub use exec::*;
pub use range_string::*;

pub trait Range<T> {
    type ElemTy: RangeElem<T> + Clone;
    /// Evaluate both the minimum and the maximum - cache along the way
    fn cache_eval(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError>;
    /// Evaluate the range minimum
    fn evaled_range_min(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    /// Evaluate the range maximum
    fn evaled_range_max(&self, analyzer: &impl GraphLike) -> Result<Self::ElemTy, GraphError>;
    /// Simplify the minimum, leaving references in place
    fn simplified_range_min(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Self::ElemTy, GraphError>;
    /// Simplify the maximum, leaving references in place
    fn simplified_range_max(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Self::ElemTy, GraphError>;
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
    fn filter_min_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx);
    /// Replace a potential recursion causing node index with a new index
    fn filter_max_recursion(&mut self, self_idx: NodeIdx, new_idx: NodeIdx);
}

pub trait RangeEval<E, T: RangeElem<E>>: Range<E, ElemTy = T> {
    fn sat(&self, analyzer: &impl GraphLike) -> bool;
    fn unsat(&self, analyzer: &impl GraphLike) -> bool {
        !self.sat(analyzer)
    }
    fn contains(&self, other: &Self, analyzer: &impl GraphLike) -> bool;
    fn contains_elem(&self, other: &T, analyzer: &impl GraphLike) -> bool;
    fn overlaps(&self, other: &Self, analyzer: &impl GraphLike) -> bool;
}