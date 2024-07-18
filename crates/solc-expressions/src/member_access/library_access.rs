use graph::{
    nodes::{ContextNode, ExprRet, FunctionNode},
    AnalyzerBackend, Edge,
};
use shared::{ExprErr, NodeIdx};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::Expression;

use std::collections::BTreeSet;

impl<T> LibraryAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}

/// Trait for getting library functions for a type
pub trait LibraryAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    /// Search for a library function by name
    fn library_func_search(
        &mut self,
        ctx: ContextNode,
        ty: NodeIdx,
        func_name: &str,
    ) -> Option<ExprRet> {
        self.possible_library_funcs(ctx, ty)
            .iter()
            .filter_map(|func| {
                if let Ok(name) = func.name(self) {
                    Some((name, func))
                } else {
                    None
                }
            })
            .find_map(|(name, func)| {
                if name == func_name {
                    Some(ExprRet::Single((*func).into()))
                } else {
                    None
                }
            })
    }

    /// Get all possible library functions
    fn possible_library_funcs(&mut self, ctx: ContextNode, ty: NodeIdx) -> BTreeSet<FunctionNode> {
        tracing::trace!("looking for library functions of type: {:?}", self.node(ty));
        let mut funcs: BTreeSet<FunctionNode> = BTreeSet::new();
        if let Some(associated_contract) = ctx.maybe_associated_contract(self).unwrap() {
            // search for contract scoped `using` statements
            funcs.extend(
                self.graph().edges_directed(ty, Direction::Outgoing).filter(|edge| {
                    matches!(*edge.weight(), Edge::LibraryFunction(scope) if scope == associated_contract.into())
                }).map(|edge| edge.target().into()).collect::<BTreeSet<FunctionNode>>()
            );
        }

        // Search for global `using` funcs
        if let Some(source) = ctx.maybe_associated_source(self) {
            funcs.extend(
                self.graph().edges_directed(ty, Direction::Outgoing).filter(|edge| {
                    matches!(*edge.weight(), Edge::LibraryFunction(scope) if scope == source.into())
                }).map(|edge| edge.target().into()).collect::<BTreeSet<FunctionNode>>()
            );
        }

        funcs
    }
}
