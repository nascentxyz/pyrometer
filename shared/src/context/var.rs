use crate::analyzer::{AnalyzerLike, GraphLike};
use crate::context::GraphError;
use crate::range::elem::RangeElem;
use crate::TyNode;

use crate::range::elem_ty::Elem;
use crate::range::elem_ty::RangeConcrete;
use crate::range::range_string::ToRangeString;
use crate::range::Range;
use crate::range::SolcRange;
use std::collections::BTreeMap;

use crate::AsDotStr;
use crate::BuiltInNode;
use crate::Builtin;
use crate::Concrete;
use crate::ContractNode;
use crate::EnumNode;
use crate::FunctionNode;

use crate::StructNode;
use crate::TypeNode;
use crate::{
    analyzer::Search, context::ContextNode, nodes::ConcreteNode, range::elem::RangeOp, ContextEdge,
    Edge, Field, FunctionParam, FunctionReturn, Node, NodeIdx, VarType,
};

use petgraph::visit::EdgeRef;
use petgraph::Direction;
use solang_parser::pt::{Loc, StorageLocation};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContextVarNode(pub usize);
impl AsDotStr for ContextVarNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
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
        analyzer: &'a impl GraphLike,
    ) -> Result<&'a ContextVar, GraphError> {
        match analyzer.node(*self) {
            Node::ContextVar(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be ContextVar but it was: {e:?}"
            ))),
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphLike,
    ) -> Result<&'a mut ContextVar, GraphError> {
        match analyzer.node_mut(*self) {
            Node::ContextVar(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be ContextVar but it was: {e:?}"
            ))),
        }
    }

    pub fn storage<'a>(
        &self,
        analyzer: &'a impl GraphLike,
    ) -> Result<&'a Option<StorageLocation>, GraphError> {
        Ok(&self.underlying(analyzer)?.storage)
    }

    pub fn is_storage(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Storage(..))
        ))
    }

    pub fn ty<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a VarType, GraphError> {
        Ok(&self.underlying(analyzer)?.ty)
    }

    pub fn ty_mut<'a>(&self, analyzer: &'a mut impl GraphLike) -> Result<&'a mut VarType, GraphError> {
        Ok(&mut self.underlying_mut(analyzer)?.ty)
    }

    pub fn is_mapping(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_mapping(analyzer)
    }

    pub fn is_dyn(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_dyn(analyzer)
    }

    pub fn is_indexable(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_indexable(analyzer)
    }

    pub fn loc(&self, analyzer: &impl GraphLike) -> Result<Loc, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .loc
            .expect("No loc for ContextVar"))
    }

    pub fn ctx(&self, analyzer: &impl GraphLike) -> ContextNode {
        ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()
                .expect("No associated ctx"),
        )
    }

    pub fn maybe_ctx(&self, analyzer: &impl GraphLike) -> Option<ContextNode> {
        let first = self.first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(first.0.into(), Direction::Outgoing)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::Variable))
            .map(|edge| ContextNode::from(edge.target()))
            .take(1)
            .next()
        // Some(ContextNode::from(
        //     analyzer
        //         .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
        //         .into_iter()
        //         .take(1)
        //         .next()?,
        // ))
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn update_deps(
        &mut self,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if let Some(mut range) = self.range(analyzer)? {
            range.update_deps(*self, ctx, analyzer);
            self.set_range_min(analyzer, range.min)?;
            self.set_range_max(analyzer, range.max)?;
        }
        Ok(())
    }

    pub fn name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.name.clone())
    }

    pub fn display_name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.display_name.clone())
    }

    pub fn range(&self, analyzer: &impl GraphLike) -> Result<Option<SolcRange>, GraphError> {
        self.underlying(analyzer)?.ty.range(analyzer)
    }

    pub fn ref_range<'a>(
        &self,
        analyzer: &'a impl GraphLike,
    ) -> Result<Option<std::borrow::Cow<'a, SolcRange>>, GraphError> {
        self.underlying(analyzer)?.ty.ref_range(analyzer)
    }

    pub fn range_min(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_min().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn range_max(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_max().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_min(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_min(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_max(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_max(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn return_assignments(&self, analyzer: &impl GraphLike) -> Vec<Self> {
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

    pub fn ext_return_assignments(&self, analyzer: &impl GraphLike) -> Vec<Self> {
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

    pub fn is_return_assignment(&self, analyzer: &impl GraphLike) -> bool {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .any(|edge| {
                Edge::Context(ContextEdge::ReturnAssign(true)) == *edge.weight()
                    || Edge::Context(ContextEdge::ReturnAssign(false)) == *edge.weight()
            })
    }

    pub fn is_ext_return_assignment(&self, analyzer: &impl GraphLike) -> bool {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .any(|edge| Edge::Context(ContextEdge::ReturnAssign(true)) == *edge.weight())
    }

    pub fn is_const(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        underlying.ty.is_const(analyzer)
    }

    pub fn is_symbolic(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_symbolic)
    }

    pub fn is_tmp(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.is_tmp())
    }

    pub fn is_return_node(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        if let Some(ctx) = self.maybe_ctx(analyzer) {
            return Ok(ctx
                .underlying(analyzer)?
                .ret
                .iter()
                .any(|(_, node)| node.name(analyzer).unwrap() == self.name(analyzer).unwrap()));
        }
        Ok(false)
    }

    pub fn is_return_node_in_any(&self, ctxs: &[ContextNode], analyzer: &impl GraphLike) -> bool {
        ctxs.iter().any(|ctx| {
            ctx.underlying(analyzer)
                .unwrap()
                .ret
                .iter()
                .any(|(_, node)| node.name(analyzer).unwrap() == self.name(analyzer).unwrap())
        })
    }

    pub fn tmp_of(&self, analyzer: &impl GraphLike) -> Result<Option<TmpConstruction>, GraphError> {
        Ok(self.underlying(analyzer)?.tmp_of())
    }

    pub fn is_len_var(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.name(analyzer)?.ends_with(".length")
            && analyzer
                .search_for_ancestor(
                    self.first_version(analyzer).into(),
                    &Edge::Context(ContextEdge::AttrAccess),
                )
                .is_some())
    }

    pub fn is_array_index_access(&self, analyzer: &impl GraphLike) -> bool {
        analyzer
            .search_for_ancestor(
                self.first_version(analyzer).into(),
                &Edge::Context(ContextEdge::IndexAccess),
            )
            .is_some()
    }

    pub fn len_var_to_array(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if self.name(analyzer)?.ends_with(".length") {
            if let Some(arr) = analyzer.search_for_ancestor(
                self.first_version(analyzer).into(),
                &Edge::Context(ContextEdge::AttrAccess),
            ) {
                Ok(Some(ContextVarNode::from(arr).latest_version(analyzer)))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    pub fn index_to_array(&self, analyzer: &impl GraphLike) -> Option<ContextVarNode> {
        let arr = analyzer
            .graph()
            .edges_directed(self.first_version(analyzer).into(), Direction::Outgoing)
            .filter(|edge| *edge.weight() == Edge::Context(ContextEdge::IndexAccess))
            .map(|edge| edge.target())
            .take(1)
            .next()?;
        Some(ContextVarNode::from(arr).latest_version(analyzer))
    }

    pub fn index_access_to_index(&self, analyzer: &impl GraphLike) -> Option<ContextVarNode> {
        let index = analyzer.find_child_exclude_via(
            self.first_version(analyzer).into(),
            &Edge::Context(ContextEdge::Index),
            &[],
            &|idx, _| Some(idx),
        )?;
        Some(ContextVarNode::from(index))
    }

    pub fn as_range_elem(
        &self,
        analyzer: &impl GraphLike,
        loc: Loc,
    ) -> Result<Elem<Concrete>, GraphError> {
        match self.underlying(analyzer)?.ty {
            VarType::Concrete(c) => Ok(Elem::Concrete(RangeConcrete {
                val: c.underlying(analyzer)?.clone(),
                loc,
            })),
            _ => Ok(Elem::from(*self)),
        }
    }

    pub fn cache_range(&self, analyzer: &mut impl GraphLike) -> Result<(), GraphError> {
        if let Some(mut range) = self.ty_mut(analyzer)?.take_range() {
            range.cache_eval(analyzer)?;
            self.set_range(analyzer, range)?;
        }
        Ok(())
    }

    pub fn set_range(
        &self,
        analyzer: &mut impl GraphLike,
        new_range: SolcRange,
    ) -> Result<(), GraphError> {
        let underlying = self.underlying_mut(analyzer)?;
        underlying.set_range(new_range);
        Ok(())
    }

    pub fn fallback_range(
        &self,
        analyzer: &mut impl GraphLike,
    ) -> Result<Option<SolcRange>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        underlying.fallback_range(analyzer)
    }

    pub fn needs_fallback(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.needs_fallback())
    }
    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_min(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_min: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        if new_min.contains_node((*self).into()) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into());
            } else {
                return Err(GraphError::UnbreakableRecursion(format!("The variable {}'s range is self-referential and we cannot break the recursion.", self.display_name(analyzer)?)));
            }
        }

        tracing::trace!(
            "setting range minimum: {} (node idx: {}), current:\n{:#?}, new_min:\n{:#?}",
            self.display_name(analyzer)?,
            self.0,
            self.range_min(analyzer)?,
            new_min
        );

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.set_range_min(analyzer, new_min)?;
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            self.underlying_mut(analyzer)?
                .set_range_min(new_min, fallback);
        }
        self.cache_range(analyzer)?;
        Ok(())
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_max(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_max: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        if new_max.contains_node((*self).into()) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into());
            }
        }

        tracing::trace!(
            "setting range maximum: {:?}, {}, current:\n{:#?}, new:\n{:#?}",
            self,
            self.display_name(analyzer)?,
            self.ref_range(analyzer)?.unwrap().range_max(), // .unwrap()
            new_max
        );

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.set_range_max(analyzer, new_max)?;
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };

            self.underlying_mut(analyzer)?
                .set_range_max(new_max, fallback)
        }

        self.cache_range(analyzer)?;
        Ok(())
    }

    pub fn set_range_exclusions(
        &self,
        analyzer: &mut impl GraphLike,
        new_exclusions: Vec<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };
        self.underlying_mut(analyzer)?
            .set_range_exclusions(new_exclusions, fallback);
        Ok(())
    }

    pub fn try_set_range_min(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_min: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        if new_min.contains_node((*self).into()) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into());
            }
        }

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.try_set_range_min(analyzer, new_min)
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            Ok(self
                .underlying_mut(analyzer)?
                .try_set_range_min(new_min, fallback))
        }
    }

    pub fn try_set_range_max(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_max: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        if new_max.contains_node((*self).into()) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into());
            }
        }

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.try_set_range_max(analyzer, new_max)
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            Ok(self
                .underlying_mut(analyzer)?
                .try_set_range_max(new_max, fallback))
        }
    }

    pub fn try_set_range_exclusions(
        &self,
        analyzer: &mut impl GraphLike,
        new_exclusions: Vec<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };
        Ok(self
            .underlying_mut(analyzer)?
            .try_set_range_exclusions(new_exclusions, fallback))
    }

    pub fn latest_version(&self, analyzer: &impl GraphLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn latest_version_less_than(&self, idx: NodeIdx, analyzer: &impl GraphLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            if next.0 <= idx.index() {
                latest = next;
            } else {
                break;
            }
        }
        latest
    }

    pub fn latest_version_in_ctx(
        &self,
        ctx: ContextNode,
        analyzer: &impl GraphLike,
    ) -> Result<Self, GraphError> {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)?) {
            Ok(cvar.latest_version(analyzer))
        } else {
            Ok(*self)
        }
    }

    pub fn latest_version_in_ctx_less_than(
        &self,
        idx: NodeIdx,
        ctx: ContextNode,
        analyzer: &impl GraphLike,
    ) -> Result<Self, GraphError> {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)?) {
            Ok(cvar.latest_version_less_than(idx, analyzer))
        } else {
            Ok(*self)
        }
    }

    pub fn first_version(&self, analyzer: &impl GraphLike) -> Self {
        let mut earlier = *self;
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
        }
        earlier
    }

    pub fn num_versions(&self, analyzer: &impl GraphLike) -> usize {
        let mut count = 1;
        let mut earlier = self.latest_version(analyzer);
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
            count += 1;
        }
        count
    }

    pub fn next_version(&self, analyzer: &impl GraphLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.source()))
            .take(1)
            .next()
    }

    pub fn previous_version(&self, analyzer: &impl GraphLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn previous_or_inherited_version(&self, analyzer: &impl GraphLike) -> Option<Self> {
        if let Some(prev) = self.previous_version(analyzer) {
            Some(prev)
        } else {
            analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| Edge::Context(ContextEdge::InheritedVariable) == *edge.weight())
                .map(|edge| ContextVarNode::from(edge.target()))
                .take(1)
                .next()
        }
    }

    pub fn range_deps(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(range) = self.ref_range(analyzer)? {
            Ok(range.dependent_on())
        } else {
            Ok(vec![])
        }
    }

    pub fn dependent_on(
        &self,
        analyzer: &impl GraphLike,
        return_self: bool,
    ) -> Result<Vec<Self>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        if let Some(tmp) = underlying.tmp_of() {
            let mut nodes = tmp.lhs.dependent_on(analyzer, true)?;
            if let Some(rhs) = tmp.rhs {
                nodes.extend(rhs.dependent_on(analyzer, true)?);
            }
            Ok(nodes)
        } else if return_self {
            Ok(vec![*self])
        } else {
            Ok(vec![])
        }
    }

    pub fn graph_dependent_on(
        &self,
        analyzer: &impl GraphLike,
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

    pub fn is_concrete(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(self.ty(analyzer)?, VarType::Concrete(_)))
    }

    pub fn as_concrete(&self, analyzer: &impl GraphLike) -> Result<Concrete, GraphError> {
        match &self.ty(analyzer)? {
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.clone()),
            e => Err(GraphError::NodeConfusion(format!(
                "Expected variable type to be concrete but was: {e:?}"
            ))),
        }
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let new_underlying = self
            .underlying(analyzer)?
            .clone()
            .as_cast_tmp(loc, ctx, cast_ty, analyzer)?;
        let node = analyzer.add_node(Node::ContextVar(new_underlying));
        ctx.add_var(node.into(), analyzer)?;
        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        Ok(node.into())
    }

    pub fn as_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let new_underlying = self
            .underlying(analyzer)?
            .clone()
            .as_tmp(loc, ctx, analyzer)?;
        Ok(analyzer.add_node(Node::ContextVar(new_underlying)).into())
    }

    pub fn ty_eq(&self, other: &Self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.ty_eq(other.ty(analyzer)?, analyzer)
    }

    pub fn ty_eq_ty(&self, other: &VarType, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.ty_eq(other, analyzer)
    }

    pub fn cast_from(
        &self,
        other: &Self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let to_ty = other.ty(analyzer)?.clone();
        self.cast_from_ty(to_ty, analyzer)?;
        Ok(())
    }

    pub fn literal_cast_from(
        &self,
        other: &Self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let to_ty = other.ty(analyzer)?.clone();
        self.literal_cast_from_ty(to_ty, analyzer)?;
        Ok(())
    }

    pub fn cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if !self.ty_eq_ty(&to_ty, analyzer)? {
            let r = self.ty_mut(analyzer)?.take_range();

            let mut new_ty = self.ty(analyzer)?.empty_ty();
            new_ty.try_cast(&to_ty, analyzer)?;
            *self.ty_mut(analyzer)? = new_ty;

            match (r, to_ty.range(analyzer)?) {
                (Some(r), Some(r2)) => {
                    let min = r.min.cast(r2.min);
                    let max = r.max.cast(r2.max);
                    self.set_range_min(analyzer, min)?;
                    self.set_range_max(analyzer, max)?;
                }
                (Some(r), None) => {
                    self.ty_mut(analyzer)?.set_range(r)?;
                }
                _ => {}
            }
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_string();
            self.underlying_mut(analyzer)?.display_name = display_name;
        }
        Ok(())
    }

    pub fn literal_cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if !self.ty_eq_ty(&to_ty, analyzer)? {
            let r = self.ty_mut(analyzer)?.take_range();

            let mut new_ty = self.ty(analyzer)?.empty_ty();
            new_ty.try_literal_cast(&to_ty, analyzer)?;
            *self.ty_mut(analyzer)? = new_ty;
            if let Some(r) = r {
                self.ty_mut(analyzer)?.set_range(r)?;
            }
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_string();
            self.underlying_mut(analyzer)?.display_name = display_name;
        }
        Ok(())
    }

    pub fn try_increase_size(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let from_ty = self.ty(analyzer)?.clone();
        self.cast_from_ty(from_ty.max_size(analyzer)?, analyzer)?;
        Ok(())
    }

    pub fn is_int(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_int(analyzer)
    }

    pub fn sol_delete_range(&mut self, analyzer: &mut impl GraphLike) -> Result<(), GraphError> {
        let ty = self.ty(analyzer)?;
        if let Some(delete_range) = ty.delete_range_result(analyzer)? {
            self.set_range(analyzer, delete_range)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextVar {
    pub loc: Option<Loc>,
    pub name: String,
    pub display_name: String,
    pub storage: Option<StorageLocation>,
    pub is_tmp: bool,
    pub tmp_of: Option<TmpConstruction>,
    pub is_symbolic: bool,
    pub is_return: bool,
    pub ty: VarType,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TmpConstruction {
    pub lhs: ContextVarNode,
    pub op: RangeOp,
    pub rhs: Option<ContextVarNode>,
}

impl TmpConstruction {
    pub fn new(lhs: ContextVarNode, op: RangeOp, rhs: Option<ContextVarNode>) -> Self {
        Self { lhs, op, rhs }
    }
}

impl ContextVar {
    pub fn eq_ignore_loc(&self, other: &Self) -> bool {
        self.name == other.name
            && self.display_name == other.display_name
            && self.storage == other.storage
            && self.is_tmp == other.is_tmp
            && self.tmp_of == other.tmp_of
            && self.is_symbolic == other.is_symbolic
            && self.is_return == other.is_return
            && self.ty == other.ty
    }

    pub fn is_tmp(&self) -> bool {
        self.is_tmp || self.tmp_of.is_some()
    }

    pub fn tmp_of(&self) -> Option<TmpConstruction> {
        self.tmp_of
    }

    pub fn new_from_concrete(
        loc: Loc,
        ctx: ContextNode,
        concrete_node: ConcreteNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let name = format!(
            "tmp_{}({})",
            ctx.new_tmp(analyzer)?,
            concrete_node.underlying(analyzer)?.as_string()
        );
        Ok(ContextVar {
            loc: Some(loc),
            name,
            display_name: concrete_node.underlying(analyzer)?.as_string(),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::Concrete(concrete_node),
        })
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let mut new_tmp = self.clone();
        new_tmp.loc = Some(loc);
        new_tmp.is_tmp = true;
        new_tmp.name = format!(
            "tmp_{}({}({}))",
            ctx.new_tmp(analyzer)?,
            cast_ty.as_string(analyzer)?,
            self.name
        );
        new_tmp.display_name = format!("{}({})", cast_ty.as_string(analyzer)?, self.display_name);
        Ok(new_tmp)
    }

    pub fn as_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let mut new_tmp = self.clone();
        new_tmp.loc = Some(loc);
        new_tmp.is_tmp = true;
        new_tmp.name = format!("tmp{}({})", ctx.new_tmp(analyzer)?, self.name);
        new_tmp.display_name = format!("tmp_{}", self.name);
        Ok(new_tmp)
    }

    pub fn new_from_contract(
        loc: Loc,
        contract_node: ContractNode,
        analyzer: &impl GraphLike,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: contract_node.name(analyzer)?,
            display_name: contract_node.name(analyzer)?,
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(
                TypeNode::Contract(contract_node),
                SolcRange::try_from_builtin(&Builtin::Address),
            ),
        })
    }

    pub fn new_from_struct(
        loc: Loc,
        struct_node: StructNode,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!(
                "tmp_struct_{}_{}",
                ctx.new_tmp(analyzer)?,
                struct_node.name(analyzer)?
            ),
            display_name: struct_node.name(analyzer)?,
            storage: Some(StorageLocation::Memory(Loc::Implicit)),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(TypeNode::Struct(struct_node), None),
        })
    }

    pub fn new_from_ty(
        loc: Loc,
        ty_node: TyNode,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!(
                "tmp_ty_{}_{}",
                ctx.new_tmp(analyzer)?,
                ty_node.name(analyzer)?
            ),
            display_name: ty_node.name(analyzer)?,
            storage: Some(StorageLocation::Memory(Loc::Implicit)),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::try_from_idx(analyzer, ty_node.0.into()).unwrap(),
        })
    }

    pub fn new_from_builtin(
        loc: Loc,
        bn_node: BuiltInNode,
        analyzer: &impl GraphLike,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: format!("tmp_{}", bn_node.underlying(analyzer)?.as_string(analyzer)?),
            display_name: format!("tmp_{}", bn_node.underlying(analyzer)?.as_string(analyzer)?),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::try_from_idx(analyzer, bn_node.into()).unwrap(),
        })
    }

    pub fn fallback_range(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<SolcRange>, GraphError> {
        match &self.ty {
            VarType::User(TypeNode::Contract(_), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    Ok(SolcRange::try_from_builtin(&Builtin::Address))
                }
            }
            VarType::User(TypeNode::Enum(enum_node), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    Ok(enum_node.maybe_default_range(analyzer)?)
                }
            }
            VarType::User(TypeNode::Ty(ty_node), ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    let underlying =
                        BuiltInNode::from(ty_node.underlying(analyzer)?.ty).underlying(analyzer)?;
                    Ok(SolcRange::try_from_builtin(underlying))
                }
            }
            VarType::BuiltIn(bn, ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Ok(Some(range.clone()))
                } else {
                    let underlying = bn.underlying(analyzer)?;
                    Ok(SolcRange::try_from_builtin(underlying))
                }
            }
            VarType::Concrete(cn) => Ok(SolcRange::from(cn.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn set_range(&mut self, new_range: SolcRange) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                *maybe_range = Some(new_range);
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {e:?}"),
        }
    }

    pub fn needs_fallback(&self) -> bool {
        match &self.ty {
            VarType::User(TypeNode::Contract(_), ref maybe_range)
            | VarType::User(TypeNode::Enum(_), ref maybe_range)
            | VarType::User(TypeNode::Ty(_), ref maybe_range)
            | VarType::BuiltIn(_, ref maybe_range) => maybe_range.is_none(),
            _ => false,
        }
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_min(&mut self, new_min: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        // tracing::trace!("Setting range min in underlying: {:?}", self.ty);
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {e:?}"),
        }
    }

    pub fn try_set_range_min(
        &mut self,
        new_min: Elem<Concrete>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn set_range_max(&mut self, new_max: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {e:?}"),
        }
    }

    pub fn set_range_exclusions(
        &mut self,
        new_exclusions: Vec<Elem<Concrete>>,
        fallback_range: Option<SolcRange>,
    ) {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {e:?}"),
        }
    }

    pub fn try_set_range_max(
        &mut self,
        new_max: Elem<Concrete>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn try_set_range_exclusions(
        &mut self,
        new_exclusions: Vec<Elem<Concrete>>,
        fallback_range: Option<SolcRange>,
    ) -> bool {
        match &mut self.ty {
            VarType::User(TypeNode::Contract(_), ref mut maybe_range)
            | VarType::User(TypeNode::Enum(_), ref mut maybe_range)
            | VarType::User(TypeNode::Ty(_), ref mut maybe_range)
            | VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => true,
            _ => false,
        }
    }

    pub fn maybe_from_user_ty(
        analyzer: &impl GraphLike,
        loc: Loc,
        node_idx: NodeIdx,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, node_idx) {
            let (name, storage) = match analyzer.node(node_idx) {
                Node::Contract(c) => {
                    let name = c.name.clone().expect("Contract had no name").name;
                    (name, None)
                }
                Node::Function(f) => {
                    let name = f.name.clone().expect("Function had no name").name;
                    (name, None)
                }
                Node::Struct(s) => {
                    let name = s.name.clone().expect("Struct had no name").name;
                    (name, None)
                }
                Node::Enum(e) => {
                    let name = e.name.clone().expect("Enum had no name").name;
                    (name, None)
                }
                Node::Var(var) => {
                    let name = var.name.clone().expect("Variable had no name").name;
                    let storage = if var.in_contract {
                        if !var.attrs.iter().any(|attr| {
                            matches!(attr, solang_parser::pt::VariableAttribute::Constant(_))
                        }) {
                            Some(StorageLocation::Storage(var.loc))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    (name, storage)
                }
                Node::Ty(ty) => {
                    let name = &ty.name.name;
                    (name.clone(), None)
                }
                _ => return None,
            };

            Some(ContextVar {
                loc: Some(loc),
                name: name.clone(),
                display_name: name,
                storage,
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                is_return: false,
                ty,
            })
        } else {
            None
        }
    }

    pub fn maybe_new_from_field(
        analyzer: &impl GraphLike,
        loc: Loc,
        parent_var: &ContextVar,
        field: Field,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, field.ty) {
            Some(ContextVar {
                loc: Some(loc),
                name: parent_var.name.clone()
                    + "."
                    + &field.name.clone().expect("Field had no name").name,
                display_name: parent_var.name.clone()
                    + "."
                    + &field.name.expect("Field had no name").name,
                storage: parent_var.storage.clone(),
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                is_return: false,
                ty,
            })
        } else {
            None
        }
    }

    pub fn new_from_enum_variant(
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        ctx: ContextNode,
        loc: Loc,
        enum_node: EnumNode,
        variant: String,
    ) -> Result<Self, GraphError> {
        let enum_name = enum_node.name(analyzer)?;
        Ok(ContextVar {
            loc: Some(loc),
            name: format!("{}.{}_{}", enum_name, variant, ctx.new_tmp(analyzer)?),
            display_name: format!("{}.{}", enum_name, variant),
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::User(
                TypeNode::Enum(enum_node),
                Some(enum_node.range_from_variant(variant, analyzer)?),
            ),
        })
    }

    pub fn new_from_index(
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        loc: Loc,
        parent_name: String,
        parent_display_name: String,
        parent_storage: StorageLocation,
        parent_var: &BuiltInNode,
        index: ContextVarNode,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(loc),
            name: parent_name + "[" + &index.name(analyzer)? + "]",
            display_name: parent_display_name + "[" + &index.display_name(analyzer)? + "]",
            storage: Some(parent_storage),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: index.underlying(analyzer)?.is_symbolic,
            is_return: false,
            ty: parent_var.dynamic_underlying_ty(analyzer)?,
        })
    }

    pub fn new_from_func(
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        func: FunctionNode,
    ) -> Result<Self, GraphError> {
        Ok(ContextVar {
            loc: Some(func.underlying(analyzer)?.loc),
            name: func.name(analyzer)?,
            display_name: func.name(analyzer)?,
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: false,
            is_return: false,
            ty: VarType::User(TypeNode::Func(func), None),
        })
    }

    pub fn maybe_new_from_func_param(
        analyzer: &impl GraphLike,
        param: FunctionParam,
    ) -> Option<Self> {
        if let Some(name) = param.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, param.ty) {
                Some(ContextVar {
                    loc: Some(param.loc),
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: param.storage,
                    is_tmp: false,
                    tmp_of: None,
                    is_symbolic: true,
                    is_return: false,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn maybe_new_from_func_ret(analyzer: &impl GraphLike, ret: FunctionReturn) -> Option<Self> {
        if let Some(name) = ret.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, ret.ty) {
                Some(ContextVar {
                    loc: Some(ret.loc),
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: ret.storage,
                    is_tmp: false,
                    tmp_of: None,
                    is_symbolic: true,
                    is_return: true,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn new_from_func_ret(
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        ret: FunctionReturn,
    ) -> Result<Option<Self>, GraphError> {
        let (is_tmp, name) = if let Some(name) = ret.name {
            (false, name.name)
        } else {
            (true, format!("tmp_func_ret_{}", ctx.new_tmp(analyzer)?))
        };

        if let Some(ty) = VarType::try_from_idx(analyzer, ret.ty) {
            Ok(Some(ContextVar {
                loc: Some(ret.loc),
                name: name.clone(),
                display_name: name,
                storage: ret.storage,
                is_tmp,
                tmp_of: None,
                is_symbolic: true,
                is_return: true,
                ty,
            }))
        } else {
            Ok(None)
        }
    }
}
