use solang_parser::pt::Loc;

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeConcrete<T> {
    pub val: T,
    pub loc: Loc,
}