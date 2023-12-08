/// A dynamic range element value
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Reference<T> {
    /// Index of the node that is referenced
    pub idx: NodeIdx,
    /// Cached minimized value
    pub minimized: Option<MinMaxed<T>>,
    /// Cached maximized value
    pub maximized: Option<MinMaxed<T>>,
}

impl<T> Reference<T> {
    pub fn new(idx: NodeIdx) -> Self {
        Self {
            idx,
            minimized: None,
            maximized: None,
        }
    }
}