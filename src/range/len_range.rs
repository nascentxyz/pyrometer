use crate::range::RangeElem;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LenRange {
    pub min: RangeElem,
    pub max: RangeElem,
}
