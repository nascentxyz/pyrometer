
use std::collections::BTreeMap;

use solang_parser::pt::Loc;

/// A range element string consisting of a string and a location
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeElemString {
    pub s: String,
    pub loc: Loc,
}

impl RangeElemString {
    /// Creates a new range element string from a string and a location
    pub fn new(s: String, loc: Loc) -> Self {
        Self { s, loc }
    }
}

/// A range string consisting of stringified range elements
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeString {
    pub min: RangeElemString,
    pub max: RangeElemString,
}

impl RangeString {
    /// Creates a new range string from a min and max [`RangeElemString`]
    pub fn new(min: RangeElemString, max: RangeElemString) -> Self {
        Self { min, max }
    }
}

/// String related functions for ranges
pub trait ToRangeString {
    /// Gets the definition string of the range element
    fn def_string(&self, analyzer: &impl GraphLike) -> RangeElemString;
    /// Converts a range to a human string
    fn to_range_string(&self, maximize: bool, analyzer: &impl GraphLike) -> RangeElemString;
}
