impl RangeElem<Concrete> for Reference<Concrete> {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.idx == other.idx {
            Some(std::cmp::Ordering::Equal)
        } else {
            None
        }
    }

    fn dependent_on(&self) -> Vec<NodeIdx> {
        vec![self.idx]
    }

    fn update_deps(&mut self, mapping: &BTreeMap<NodeIdx, NodeIdx>) {
        if let Some(new) = mapping.get(self.idx) {
            self.idx = new;
        }
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        let cvar = ContextVarNode::from(self.idx);
        if cvar.is_independent_and_storage_or_calldata(analyzer)? {
            return Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )));
        }
        if maximize {
            cvar.range_max(analyzer)?
                .unwrap()
                .flatten(maximize, analyzer)
        } else {
            let flattened = cvar
                .range_min(analyzer)?
                .unwrap()
                .flatten(maximize, analyzer)?;
            Ok(flattened)
        }
    }

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx) {}

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok(*cached);
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_max(analyzer)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok(*cached);
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_min(analyzer)
                } else {
                    Ok(Elem::Reference(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Reference(self.clone())),
        }
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        let cvar = ContextVarNode::from(self.idx);

        let independent = cvar.is_independent_and_storage_or_calldata(analyzer)?;
        if independent {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(true, analyzer)?
                .simplify_maximize(exclude, analyzer)
        }
    }

    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        let cvar = ContextVarNode::from(self.idx);
        if cvar.is_independent_and_storage_or_calldata(analyzer)? {
            Ok(Elem::Reference(Reference::new(
                cvar.global_first_version(analyzer).into(),
            )))
        } else {
            self.flatten(false, analyzer)?
                .simplify_minimize(exclude, analyzer)
        }
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.maximized = Some(MinMaxed::Maximized(Box::new(self.maximize(g)?)));
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.minimized = Some(MinMaxed::Minimized(Box::new(self.minimize(g)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
    }

    fn contains_op_set(
        &self,
        max: bool,
        op_set: &[RangeOp],
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    if max {
                        range.max.contains_op_set(max, op_set, analyzer)
                    } else {
                        range.min.contains_op_set(max, op_set, analyzer)
                    }
                } else {
                    Ok(false)
                }
            }
            VarType::Concrete(_concrete_node) => Ok(false),
            _e => Ok(false),
        }
    }
}