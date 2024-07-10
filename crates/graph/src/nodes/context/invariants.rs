use std::collections::BTreeSet;

use crate::{
    nodes::{Concrete, ContextNode, ContextVarNode},
    range::elem::Elem,
    ContextEdge, Edge, GraphBackend, RepresentationInvariant,
};
use shared::{ContextReprErr, GraphError, NodeIdx, RangeArena, RepresentationErr};

use petgraph::{visit::EdgeRef, Direction};

impl ContextNode {
    fn cache_matches_edges(
        &self,
        g: &impl GraphBackend,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        let mut vars: BTreeSet<_> = self
            .underlying(g)?
            .cache
            .vars
            .values()
            .cloned()
            .collect::<BTreeSet<_>>();
        vars.extend(
            self.underlying(g)?
                .cache
                .tmp_vars
                .values()
                .cloned()
                .collect::<BTreeSet<_>>(),
        );
        let edge_vars: BTreeSet<_> = g
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|e| ContextVarNode::from(e.source()))
            .collect::<BTreeSet<_>>();

        let diff: Vec<_> = edge_vars.difference(&vars).map(|i| i.0.into()).collect();
        if !diff.is_empty() {
            Ok(Some(
                ContextReprErr::VarCacheErr(self.0.into(), diff).into(),
            ))
        } else {
            Ok(None)
        }
    }

    fn variables_invariants(
        &self,
        g: &impl GraphBackend,
        arena: &RangeArena<Elem<Concrete>>,
    ) -> Result<Vec<RepresentationErr>, GraphError> {
        let vars: Vec<_> = self.vars(g).values().collect();
        Ok(vars
            .iter()
            .map(|var| var.is_representation_ok(g, arena))
            .collect::<Result<Vec<Option<_>>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>())
    }
}

impl RepresentationInvariant for ContextNode {
    fn is_representation_ok(
        &self,
        g: &impl GraphBackend,
        arena: &RangeArena<Elem<Concrete>>,
    ) -> Result<Option<RepresentationErr>, GraphError> {
        // if let Some(err) = self.cache_matches_edges(g)? {
        //     return Ok(Some(err));
        // }

        let bad_vars = self.variables_invariants(g, arena)?;
        if !bad_vars.is_empty() {
            return Ok(Some(
                ContextReprErr::VarInvariantErr(self.0.into(), bad_vars).into(),
            ));
        }

        Ok(None)
    }
}
