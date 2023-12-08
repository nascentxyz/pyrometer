/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeDyn<T> {
    /// Cached minimized value
    pub minimized: Option<MinMaxed<T>>,
    /// Cached maximized value
    pub maximized: Option<MinMaxed<T>>,
    /// Length of the dynamic variable
    pub len: Elem<T>,
    /// Values of the dynamic variable
    pub val: BTreeMap<Elem<T>, Elem<T>>,
    /// Sourcecode location
    pub loc: Loc,
}
impl<T> RangeDyn<T> {
    /// Set the length
    pub fn set_len(&mut self, new_len: Elem<T>) {
        self.len = new_len;
    }

    /// Check if the node contains a reference to a node index
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.len.contains_node(node_idx)
        // || self.val.iter().any(|(k, v)| k.contains_node(node_idx) || v.contains_node(node_idx))
    }
}

