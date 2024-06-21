use crate::{nodes::ContextVarNode, range::elem::Elem, GraphBackend, GraphError};

use shared::{NodeIdx, RangeArena};
use std::hash::Hash;

pub trait RangeElem<T: Ord + Hash>: Hash {
    type GraphError;
    /// Flattens an element into an expression or concrete based purely on inputs, calldata, storage, or environment data variables
    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Returns whether `cache_flatten` has been called
    fn is_flatten_cached(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> bool;
    fn is_min_max_cached(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> (bool, bool);
    /// Flattens an element and caches the result
    fn cache_flatten(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<(), Self::GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its maximum value
    fn maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Maximizes the element and caches the result for quicker use later
    fn cache_maximize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<(), Self::GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its minimum value
    fn minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Minimizes the element and caches the result for quicker use later
    fn cache_minimize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<(), Self::GraphError>;
    /// Uncaches the minimum and maximum
    fn uncache(&mut self);
    /// Tries to simplify to maximum(i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Tries to simplify to minimum (i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Checks if two range elements are equal
    fn range_eq(&self, other: &Self, arena: &mut RangeArena<Elem<T>>) -> bool;
    /// Tries to compare the ordering of two range elements
    fn range_ord(
        &self,
        other: &Self,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Option<std::cmp::Ordering>;
    /// Traverses the range expression and finds all nodes that are dynamically pointed to
    /// and returns it in a vector.
    fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Vec<ContextVarNode>;

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<Vec<ContextVarNode>, Self::GraphError>;

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<bool, Self::GraphError>;

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<bool, Self::GraphError>;
    /// Attempts to replace range elements that form a cyclic dependency by replacing
    /// it with a new node. Ideally no cyclic dependencies occur in ranges as of now
    /// but in theory it can make sense.
    ///
    /// e.g.: take the basic expression `x + y`, in normal checked solidity math
    /// both x and y have the requirement `var <= 2**256 - 1 - other_var`, forming a
    /// cyclic dependency.
    fn filter_recursion(
        &mut self,
        node_idx: NodeIdx,
        new_idx: NodeIdx,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    );

    fn arenaize(
        &mut self,
        analyzer: &mut impl GraphBackend,
        arena: &mut RangeArena<Elem<T>>,
    ) -> Result<(), GraphError>;
}
