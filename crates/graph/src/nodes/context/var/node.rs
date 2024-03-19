use crate::{
    nodes::{ContextNode, ContextVar, TmpConstruction, VarNode},
    range::{elem::RangeElem, range_string::ToRangeString, Range},
    AsDotStr, ContextEdge, Edge, GraphBackend, GraphError, Node,
};

use shared::{NodeIdx, Search, StorageLocation};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::Loc;

use std::collections::BTreeMap;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContextVarNode(pub usize);

impl AsDotStr for ContextVarNode {
    fn as_dot_str(&self, analyzer: &impl GraphBackend) -> String {
        let underlying = self.underlying(analyzer).unwrap();

        let range_str = if let Some(r) = underlying.ty.ref_range(analyzer).unwrap() {
            format!(
                "[{}, {}]",
                r.evaled_range_min(analyzer)
                    .unwrap()
                    .to_range_string(false, analyzer)
                    .s,
                r.evaled_range_max(analyzer)
                    .unwrap()
                    .to_range_string(true, analyzer)
                    .s
            )
        } else {
            "".to_string()
        };

        format!(
            "{} - {} -- {} -- range: {}",
            underlying.display_name,
            self.0,
            underlying.ty.as_string(analyzer).unwrap(),
            range_str
        )
    }
}

impl From<ContextVarNode> for NodeIdx {
    fn from(val: ContextVarNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextVarNode {
    fn from(idx: NodeIdx) -> Self {
        ContextVarNode(idx.index())
    }
}

impl ContextVarNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a ContextVar, GraphError> {
        match analyzer.node(*self) {
            Node::ContextVar(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be ContextVar but it was: {e:?}"
            ))),
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut ContextVar, GraphError> {
        match analyzer.node_mut(*self) {
            Node::ContextVar(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be ContextVar but it was: {e:?}"
            ))),
        }
    }

    pub fn storage<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Option<StorageLocation>, GraphError> {
        Ok(&self.underlying(analyzer)?.storage)
    }

    pub fn loc(&self, analyzer: &impl GraphBackend) -> Result<Loc, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .loc
            .expect("No loc for ContextVar"))
    }

    pub fn ctx(&self, analyzer: &impl GraphBackend) -> ContextNode {
        ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()
                .expect("No associated ctx"),
        )
    }

    pub fn maybe_ctx(&self, analyzer: &impl GraphBackend) -> Option<ContextNode> {
        let first = self.first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(first.0.into(), Direction::Outgoing)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|edge| ContextNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn maybe_storage_var(&self, analyzer: &impl GraphBackend) -> Option<VarNode> {
        Some(
            analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .find(|edge| {
                    *edge.weight() == Edge::Context(ContextEdge::InheritedStorageVariable)
                })?
                .target()
                .into(),
        )
    }

    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.name.clone())
    }

    pub fn as_controllable_name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        if let Some(ref_range) = self.ref_range(analyzer)? {
            let min_name = ref_range
                .range_min()
                .simplify_minimize(analyzer)?
                .to_range_string(false, analyzer)
                .s;

            let max_name = ref_range
                .range_max()
                .simplify_maximize(analyzer)?
                .to_range_string(true, analyzer)
                .s;
            if max_name == min_name {
                Ok(max_name)
            } else {
                self.display_name(analyzer)
            }
        } else {
            self.display_name(analyzer)
        }
    }

    pub fn display_name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.display_name.clone())
    }

    pub fn return_assignments(&self, analyzer: &impl GraphBackend) -> Vec<Self> {
        let latest = self.latest_version(analyzer);
        let mut earlier = latest;
        let mut return_assignments = vec![];
        while let Some(prev) = earlier.previous_version(analyzer) {
            if earlier.is_return_assignment(analyzer) {
                return_assignments.push(earlier)
            }
            earlier = prev;
        }
        return_assignments
    }

    pub fn ext_return_assignments(&self, analyzer: &impl GraphBackend) -> Vec<Self> {
        let latest = self.latest_version(analyzer);
        let mut earlier = latest;
        let mut return_assignments = vec![];
        if earlier.is_ext_return_assignment(analyzer) {
            return_assignments.push(earlier)
        }
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
            if earlier.is_ext_return_assignment(analyzer) {
                return_assignments.push(earlier)
            }
        }
        return_assignments
    }

    pub fn tmp_of(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<TmpConstruction>, GraphError> {
        Ok(self.underlying(analyzer)?.tmp_of())
    }

    pub fn struct_to_fields(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<ContextVarNode>, GraphError> {
        if self.ref_range(analyzer)?.is_none() {
            let fields = analyzer
                .graph()
                .edges_directed(self.first_version(analyzer).into(), Direction::Incoming)
                .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::AttrAccess("field")))
                .map(|edge| ContextVarNode::from(edge.source()).latest_version(analyzer))
                .collect::<Vec<_>>();
            Ok(fields)
        } else {
            Ok(vec![])
        }
    }

    pub fn array_to_len_var(&self, analyzer: &impl GraphBackend) -> Option<ContextVarNode> {
        if let Some(len) = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .find(|edge| *edge.weight() == Edge::Context(ContextEdge::AttrAccess("length")))
            .map(|edge| edge.source())
        {
            Some(len.into())
        } else if let Some(prev) = self.previous_version(analyzer) {
            prev.array_to_len_var(analyzer)
        } else {
            None
        }
    }

    pub fn slot_to_storage(&self, analyzer: &impl GraphBackend) -> Option<ContextVarNode> {
        let slot = analyzer
            .graph()
            .edges_directed(self.first_version(analyzer).into(), Direction::Outgoing)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::SlotAccess))
            .map(|edge| edge.target())
            .take(1)
            .next()?;
        Some(ContextVarNode::from(slot).latest_version(analyzer))
    }

    pub fn index_access_to_array(&self, analyzer: &impl GraphBackend) -> Option<ContextVarNode> {
        if let Some(arr) = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .find(|edge| *edge.weight() == Edge::Context(ContextEdge::IndexAccess))
            .map(|edge| edge.target())
        {
            Some(arr.into())
        } else if let Some(prev) = self.previous_version(analyzer) {
            prev.index_access_to_array(analyzer)
        } else {
            None
        }
    }

    pub fn len_var_to_array(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(arr) = analyzer.search_for_ancestor(
            self.0.into(),
            &Edge::Context(ContextEdge::AttrAccess("length")),
        ) {
            Ok(Some(ContextVarNode::from(arr).latest_version(analyzer)))
        } else {
            Ok(None)
        }
    }

    pub fn index_to_array(&self, analyzer: &impl GraphBackend) -> Option<ContextVarNode> {
        let arr = analyzer
            .graph()
            .edges_directed(self.first_version(analyzer).into(), Direction::Outgoing)
            .find(|edge| *edge.weight() == Edge::Context(ContextEdge::IndexAccess))
            .map(|edge| edge.target())?;
        Some(ContextVarNode::from(arr).latest_version(analyzer))
    }

    /// Goes from an index access (i.e. `x[idx]`) to the index (i.e. `idx`)
    pub fn index_access_to_index(&self, analyzer: &impl GraphBackend) -> Option<ContextVarNode> {
        let index = analyzer.find_child_exclude_via(
            self.first_version(analyzer).into(),
            &Edge::Context(ContextEdge::Index),
            &[],
            &|idx, _| Some(idx),
        )?;
        Some(ContextVarNode::from(index))
    }

    pub fn index_or_attr_access(&self, analyzer: &impl GraphBackend) -> Vec<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| {
                matches!(
                    *edge.weight(),
                    Edge::Context(ContextEdge::IndexAccess)
                        | Edge::Context(ContextEdge::AttrAccess(_))
                )
            })
            .map(|edge| ContextVarNode::from(edge.source()))
            .collect()
    }

    pub fn set_dependent_on(&self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        let mut return_self = false;
        let mut first_iter = true;
        let mut stack = vec![*self];
        let mut result = vec![];

        while let Some(node) = stack.pop() {
            if result.contains(&node) {
                continue;
            }

            let underlying = node.underlying(analyzer)?;
            if let Some(tmp) = underlying.tmp_of() {
                stack.push(tmp.lhs);
                if let Some(rhs) = tmp.rhs {
                    stack.push(rhs);
                }
            } else if return_self {
                result.push(node);
            }

            if first_iter {
                first_iter = false;
                return_self = true;
            }
        }

        self.underlying_mut(analyzer)?.dep_on = Some(result);
        Ok(())
    }

    pub fn dependent_on(
        &self,
        analyzer: &impl GraphBackend,
        mut return_self: bool,
    ) -> Result<Vec<Self>, GraphError> {
        if let Some(dep_on) = &self.underlying(analyzer)?.dep_on {
            return Ok(dep_on.to_vec());
        }
        let mut first_iter = true;
        let mut stack = vec![*self];
        let mut result = vec![];

        while let Some(node) = stack.pop() {
            if result.contains(&node) {
                continue;
            }

            let underlying = node.underlying(analyzer)?;
            if let Some(tmp) = underlying.tmp_of() {
                stack.push(tmp.lhs);
                if let Some(rhs) = tmp.rhs {
                    stack.push(rhs);
                }
            } else if return_self {
                result.push(node);
            }

            if first_iter {
                first_iter = false;
                return_self = true;
            }
        }

        Ok(result)
    }

    pub fn graph_dependent_on(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<BTreeMap<Self, TmpConstruction>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        let mut tree = BTreeMap::default();
        if let Some(tmp) = underlying.tmp_of() {
            tree.insert(*self, tmp);
            tmp.lhs
                .graph_dependent_on(analyzer)?
                .into_iter()
                .for_each(|(key, v)| {
                    if let Some(_v) = tree.get_mut(&key) {
                        panic!("here")
                    } else {
                        tree.insert(key, v);
                    }
                });
            if let Some(rhs) = tmp.rhs {
                rhs.graph_dependent_on(analyzer)?
                    .into_iter()
                    .for_each(|(key, v)| {
                        if let Some(_v) = tree.get_mut(&key) {
                            panic!("here")
                        } else {
                            tree.insert(key, v);
                        }
                    });
            }
        }

        Ok(tree)
    }
}
