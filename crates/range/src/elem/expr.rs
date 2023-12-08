

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
