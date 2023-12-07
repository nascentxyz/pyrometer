impl ContextVarNode {
	pub fn ty<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a VarType, GraphError> {
        Ok(&self.underlying(analyzer)?.ty)
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

    pub fn is_storage(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Storage(..))
        ))
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

    pub fn is_storage_or_calldata_input(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        let global_first = self.global_first_version(analyzer);
        Ok(global_first.is_storage(analyzer)? || global_first.is_calldata_input(analyzer))
    }

    pub fn is_independent_and_storage_or_calldata(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        let global_first = self.global_first_version(analyzer);
        let is_independent = self.is_independent(analyzer)?;

        Ok((global_first.is_storage(analyzer)?
            || global_first.is_calldata_input(analyzer)
            || (
                // if its a function input, and we are evaluating the function
                // as a standalone (i.e. its internal, but we are treating it like its external)
                // it wont be marked as calldata, but for the purposes
                // of determining controllability it is to better to assume there is some path that lets us
                // control it
                global_first.is_func_input(analyzer)
                    && global_first.maybe_ctx(analyzer).is_some()
                    && !global_first.ctx(analyzer).has_parent(analyzer)?
            ))
            && is_independent)
    }

    pub fn is_independent(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.dependent_on(analyzer, false)?.is_empty() && self.tmp_of(analyzer)?.is_none())
    }

    pub fn is_controllable(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        if self.is_storage_or_calldata_input(analyzer)? {
            Ok(true)
        } else if let Some(tmp) = self.tmp_of(analyzer)? {
            let rhs_controllable = if let Some(rhs) = tmp.rhs {
                rhs.is_controllable(analyzer)?
            } else {
                false
            };
            let lhs_controllable = tmp.lhs.is_controllable(analyzer)?;
            Ok(lhs_controllable || rhs_controllable)
        } else {
            Ok(false)
        }
    }

    pub fn is_calldata_input(&self, analyzer: &impl GraphLike) -> bool {
        let global_first = self.global_first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(global_first.0.into(), Direction::Outgoing)
            .any(|edge| Edge::Context(ContextEdge::CalldataVariable) == *edge.weight())
    }

    pub fn is_func_input(&self, analyzer: &impl GraphLike) -> bool {
        let first = self.first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(first.0.into(), Direction::Outgoing)
            .any(|edge| {
                Edge::Context(ContextEdge::InputVariable) == *edge.weight()
                    || Edge::Context(ContextEdge::CalldataVariable) == *edge.weight()
            })
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
            return Ok(ctx.underlying(analyzer)?.ret.iter().any(|(_, node)| {
                if let Some(node) = node {
                    node.name(analyzer).unwrap() == self.name(analyzer).unwrap()
                } else {
                    false
                }
            }));
        }
        Ok(false)
    }

    pub fn is_return_node_in_any(&self, ctxs: &[ContextNode], analyzer: &impl GraphLike) -> bool {
        ctxs.iter().any(|ctx| {
            ctx.underlying(analyzer)
                .unwrap()
                .ret
                .iter()
                .any(|(_, node)| {
                    if let Some(node) = node {
                        node.name(analyzer).unwrap() == self.name(analyzer).unwrap()
                    } else {
                        false
                    }
                })
        })
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

    pub fn ty_eq(&self, other: &Self, analyzer: &mut impl GraphLike) -> Result<bool, GraphError> {
        self.ty(analyzer)?.ty_eq(other.ty(analyzer)?, analyzer)
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
        let from_ty = self.ty(analyzer)?.clone();
        if !from_ty.ty_eq(&to_ty, analyzer)? {
            if let Some(new_ty) = from_ty.try_cast(&to_ty, analyzer)? {
                self.underlying_mut(analyzer)?.ty = new_ty;
            }
            if let (Some(r), Some(r2)) = (self.range(analyzer)?, to_ty.range(analyzer)?) {
                let min = r.min.cast(r2.min);
                let max = r.max.cast(r2.max);
                self.set_range_min(analyzer, min)?;
                self.set_range_max(analyzer, max)?;
            }
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_human_string();
            self.underlying_mut(analyzer)?.display_name = display_name;
        }
        Ok(())
    }

    pub fn literal_cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let from_ty = self.ty(analyzer)?.clone();
        if !from_ty.ty_eq(&to_ty, analyzer)? {
            if let Some(new_ty) = from_ty.try_literal_cast(&to_ty, analyzer)? {
                self.underlying_mut(analyzer)?.ty = new_ty;
            }
            // we dont need to update the ranges because a literal by definition is concrete
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_human_string();
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
}