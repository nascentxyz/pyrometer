/// A range expression composed of other range [`Elem`]
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeExpr<T> {
    pub maximized: Option<MinMaxed<T>>,
    pub minimized: Option<MinMaxed<T>>,
    pub lhs: Box<Elem<T>>,
    pub op: RangeOp,
    pub rhs: Box<Elem<T>>,
}

impl<T> RangeExpr<T> {
    /// Creates a new range expression given a left hand side range [`Elem`], a [`RangeOp`], and a a right hand side range [`Elem`].
    pub fn new(lhs: Elem<T>, op: RangeOp, rhs: Elem<T>) -> RangeExpr<T> {
        RangeExpr {
            maximized: None,
            minimized: None,
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        }
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.lhs.contains_node(node_idx) || self.rhs.contains_node(node_idx)
    }
}

impl RangeElem<Concrete> for RangeExpr<Concrete> {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on();
        deps.extend(self.rhs.dependent_on());
        deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        self.lhs.update_deps(mapping);
        self.rhs.update_deps(mapping);
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.lhs.filter_recursion(node_idx, new_idx);
        self.rhs.filter_recursion(node_idx, new_idx);
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            Ok(*cached)
        } else {
            self.exec_op(true, analyzer)
        }
    }
    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            Ok(*cached)
        } else {
            self.exec_op(false, analyzer)
        }
    }

    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        self.simplify_exec_op(true, analyzer)
    }
    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        self.simplify_exec_op(false, analyzer)
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.cache_exec_op(true, g)?;
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.cache_exec_op(false, g)?;
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.uncache_exec();
    }
}