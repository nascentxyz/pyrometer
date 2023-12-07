/// A dynamic range element value
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Reference {
    /// Index of the node that is referenced
    pub idx: NodeIdx,
    pub minimized: Option<MinMaxed<Concrete>>,
    pub maximized: Option<MinMaxed<Concrete>>,
}

impl Reference {
    pub fn new(idx: NodeIdx) -> Self {
        Self {
            idx,
            minimized: None,
            maximized: None,
        }
    }
}

impl RangeElem<Concrete> for Reference {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        vec![ContextVarNode::from(self.idx)]
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        if let Some(new) = mapping.get(&ContextVarNode::from(self.idx)) {
            self.idx = NodeIdx::from(new.0);
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

    fn simplify_maximize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        // let cvar = ContextVarNode::from(self.idx);
        // if cvar.is_symbolic(analyzer)? {
        Ok(Elem::Reference(self.clone()))
        // }
        // if !cvar.is_tmp(analyzer)? {
        //     return Ok(Elem::Reference(self.clone()))
        // }
        // let cvar = cvar.underlying(analyzer)?;
        // match &cvar.ty {
        //     VarType::User(TypeNode::Contract(_), maybe_range)
        //     | VarType::User(TypeNode::Enum(_), maybe_range)
        //     | VarType::User(TypeNode::Ty(_), maybe_range)
        //     | VarType::BuiltIn(_, maybe_range) => {
        //         if let Some(range) = maybe_range {
        //             range.simplified_range_max(analyzer)
        //         } else {
        //             Ok(Elem::Reference(self.clone()))
        //         }
        //     }
        //     VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
        //         val: concrete_node.underlying(analyzer)?.clone(),
        //         loc: cvar.loc.unwrap_or(Loc::Implicit),
        //     })),
        //     _e => Ok(Elem::Reference(self.clone())),
        // }
    }
    fn simplify_minimize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        // let cvar = ContextVarNode::from(self.idx);
        // if cvar.is_symbolic(analyzer)? {
        Ok(Elem::Reference(self.clone()))
        // }
        // if !cvar.is_tmp(analyzer)? {
        //     return Ok(Elem::Reference(self.clone()))
        // }
        // let cvar = cvar.underlying(analyzer)?;

        // match &cvar.ty {
        //     VarType::User(TypeNode::Contract(_), maybe_range)
        //     | VarType::User(TypeNode::Enum(_), maybe_range)
        //     | VarType::User(TypeNode::Ty(_), maybe_range)
        //     | VarType::BuiltIn(_, maybe_range) => {
        //         if let Some(range) = maybe_range {
        //             range.simplified_range_min(analyzer)
        //         } else {
        //             Ok(Elem::Reference(self.clone()))
        //         }
        //     }
        //     VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
        //         val: concrete_node.underlying(analyzer)?.clone(),
        //         loc: cvar.loc.unwrap_or(Loc::Implicit),
        //     })),
        //     _e => Ok(Elem::Reference(self.clone())),
        // }
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
}