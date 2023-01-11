pub mod num_range;
pub mod range_elem;
pub mod range_expr;
use range_expr::*;
pub mod len_range;

pub use len_range::LenRange;
pub use num_range::Range;
pub use range_elem::RangeElem;

use solang_parser::pt::Loc;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DynamicRangeSide {
    Min,
    Max,
}

impl ToString for DynamicRangeSide {
    fn to_string(&self) -> String {
        match self {
            Self::Min => "range_min".to_string(),
            Self::Max => "range_max".to_string(),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeElemString {
    pub s: String,
    pub loc: Loc,
}

impl RangeElemString {
    pub fn new(s: String, loc: Loc) -> Self {
        Self { s, loc }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeString {
    pub min: RangeElemString,
    pub max: RangeElemString,
}

impl RangeString {
    pub fn new(min: RangeElemString, max: RangeElemString) -> Self {
        Self { min, max }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Op {
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Min,
    Max,
    Lt,
    Lte,
    Gt,
    Gte,
    Eq,
}

impl Op {
    pub fn inverse(self) -> Self {
        use Op::*;
        match self {
            Add => Sub,
            Mul => Div,
            Sub => Add,
            Div => Mul,
            e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }
}

impl ToString for Op {
    fn to_string(&self) -> String {
        use Op::*;
        match self {
            Add => "+".to_string(),
            Mul => "*".to_string(),
            Sub => "-".to_string(),
            Div => "/".to_string(),
            Mod => "%".to_string(),
            Min => "min".to_string(),
            Max => "max".to_string(),
            Lt => "<".to_string(),
            Gt => ">".to_string(),
            Lte => "<=".to_string(),
            Gte => ">=".to_string(),
            Eq => "==".to_string(),
        }
    }
}
