use crate::{
    nodes::ContextVarNode,
    range::elem::{Elem, RangeExpr, RangeOp},
    GraphBackend, GraphError,
};

use shared::NodeIdx;

use std::collections::BTreeMap;

pub trait RangeElem<T: Ord> {
    type GraphError;
    /// Flattens an element into an expression or concrete based purely on inputs, calldata, storage, or environment data variables
    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Returns whether `cache_flatten` has been called
    fn is_flatten_cached(&self, analyzer: &impl GraphBackend) -> bool;
    fn is_min_max_cached(&self, analyzer: &impl GraphBackend) -> (bool, bool);
    /// Flattens an element and caches the result
    fn cache_flatten(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), Self::GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its maximum value
    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<T>, Self::GraphError>;
    /// Maximizes the element and caches the result for quicker use later
    fn cache_maximize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), Self::GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its minimum value
    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<T>, Self::GraphError>;
    /// Minimizes the element and caches the result for quicker use later
    fn cache_minimize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), Self::GraphError>;
    /// Uncaches the minimum and maximum
    fn uncache(&mut self);
    /// Tries to simplify to maximum(i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_maximize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Tries to simplify to minimum (i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_minimize(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<T>, Self::GraphError>;
    /// Checks if two range elements are equal
    fn range_eq(&self, other: &Self, analyzer: &impl GraphBackend) -> bool;
    /// Tries to compare the ordering of two range elements
    fn range_ord(&self, other: &Self, analyzer: &impl GraphBackend) -> Option<std::cmp::Ordering>;
    /// Constructs a range `Elem::Expr` given a lhs, rhs, and operation ([`RangeOp`]).
    fn range_op(lhs: Elem<T>, rhs: Elem<T>, op: RangeOp, _analyzer: &impl GraphBackend) -> Elem<T>
    where
        Self: Sized,
    {
        Elem::Expr(RangeExpr::new(lhs, op, rhs))
    }
    /// Traverses the range expression and finds all nodes that are dynamically pointed to
    /// and returns it in a vector.
    fn dependent_on(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode>;

    fn recursive_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, Self::GraphError>;

    fn has_cycle(
        &self,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, Self::GraphError>;

    fn depends_on(
        &self,
        var: ContextVarNode,
        seen: &mut Vec<ContextVarNode>,
        analyzer: &impl GraphBackend,
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
    );

    fn arenaize(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError>;
}
