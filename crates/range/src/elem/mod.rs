use std::collections::BTreeMap;

mod concrete;
mod elem_enum;
mod expr;
mod map_or_array;
mod reference;

pub use concrete::*;
pub use elem_enum::*;
pub use expr::*;
pub use map_or_array::*;
pub use reference::*;


#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum MinMaxed<T> {
    Minimized(Box<Elem<T>>),
    Maximized(Box<Elem<T>>),
}

/// An operation to be performed on a range element
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RangeOp {
    /// Addition
    Add(bool),
    /// Multiplication
    Mul(bool),
    /// Subtraction
    Sub(bool),
    /// Division
    Div(bool),
    /// Modulos
    Mod,
    /// Minimum
    Min,
    /// Maximum
    Max,
    /// Less than
    Lt,
    /// Less than or equal
    Lte,
    /// Geater than
    Gt,
    /// Greater than or equal
    Gte,
    /// Equal
    Eq,
    /// Not Equal
    Neq,
    /// Logical Not
    Not,
    /// Bitwise shift left
    Shl,
    /// Bitwise shift right
    Shr,
    /// Logical AND
    And,
    /// Logical OR
    Or,
    /// Catch-all requirement statement
    Where,
    /// Cast from one type to another
    Cast,
    /// Bitwise AND
    BitAnd,
    /// Bitwise OR
    BitOr,
    /// Bitwise XOR
    BitXor,
    /// Bitwise Not
    BitNot,
    /// Exponentiation
    Exp,
    /// Concatenation
    Concat,
}

impl RangeOp {
    /// Attempts to return the inverse range operation (e.g.: `RangeOp::Add => RangeOp::Sub`)
    pub fn inverse(self) -> Option<Self> {
        use RangeOp::*;
        match self {
            Add(i) => Some(Sub(i)),
            Mul(i) => Some(Div(i)),
            Sub(i) => Some(Add(i)),
            Div(i) => Some(Mul(i)),
            Shl => Some(Shr),
            Shr => Some(Shl),
            Eq => Some(Neq),
            Neq => Some(Eq),
            Lt => Some(Gt),
            Lte => Some(Gte),
            Gt => Some(Lt),
            Gte => Some(Lte),
            _ => None, // e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }

    /// Gets the logical inverse of a boolean operation
    pub fn logical_inverse(self) -> Option<Self> {
        use RangeOp::*;
        match self {
            Eq => Some(Neq),
            Neq => Some(Eq),
            Lt => Some(Gte),
            Lte => Some(Gt),
            Gt => Some(Lte),
            Gte => Some(Lt),
            Or => Some(And),
            And => Some(Or),
            _ => None, // e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }

    pub fn require_parts(self) -> Option<(Self, Self, (Self, Self))> {
        use RangeOp::*;
        let t = match self {
            Eq => (Eq, Neq, (Neq, Eq)),
            Neq => (Neq, Eq, (Eq, Neq)),
            Lte => (Lte, Gte, (Gte, Lte)),
            Gte => (Gte, Lte, (Lte, Gte)),
            Gt => (Gt, Lt, (Lt, Gt)),
            Lt => (Lt, Gt, (Gt, Lt)),
            _ => return None,
        };
        Some(t)
    }
}

impl ToString for RangeOp {
    fn to_string(&self) -> String {
        use RangeOp::*;
        match self {
            Add(..) => "+".to_string(),
            Mul(..) => "*".to_string(),
            Sub(..) => "-".to_string(),
            Div(..) => "/".to_string(),
            Shl => "<<".to_string(),
            Shr => ">>".to_string(),
            Mod => "%".to_string(),
            Exp => "**".to_string(),
            Min => "min".to_string(),
            Max => "max".to_string(),
            Lt => "<".to_string(),
            Gt => ">".to_string(),
            Lte => "<=".to_string(),
            Gte => ">=".to_string(),
            Eq => "==".to_string(),
            Neq => "!=".to_string(),
            Not => "!".to_string(),
            And => "&&".to_string(),
            Or => "||".to_string(),
            Where => "where".to_string(),
            Cast => "cast".to_string(),
            BitAnd => "&".to_string(),
            BitOr => "|".to_string(),
            BitXor => "^".to_string(),
            BitNot => "~".to_string(),
            Concat => "concat".to_string(),
        }
    }
}

pub trait RangeElem<T> {
    /// Flattens an element into an expression or concrete based purely on inputs, calldata, storage, or environment data variables
    fn flatten(&self, maximize: bool, analyzer: &impl GraphLike) -> Result<Elem<T>, GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its maximum value
    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<T>, GraphError>;
    /// Maximizes the element and caches the result for quicker use later
    fn cache_maximize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its minimum value
    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<T>, GraphError>;
    /// Minimizes the element and caches the result for quicker use later
    fn cache_minimize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError>;
    /// Uncaches the minimum and maximum
    fn uncache(&mut self);
    /// Tries to simplify to maximum(i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<T>, GraphError>;
    /// Tries to simplify to minimum (i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<T>, GraphError>;
    /// Checks if two range elements are equal
    fn range_eq(&self, other: &Self) -> bool;
    /// Tries to compare the ordering of two range elements
    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering>;
    /// Constructs a range `Elem::Expr` given a lhs, rhs, and operation ([`RangeOp`]).
    fn range_op(lhs: Elem<T>, rhs: Elem<T>, op: RangeOp) -> Elem<T>
    where
        Self: Sized,
    {
        Elem::Expr(RangeExpr::new(lhs, op, rhs))
    }
    /// Traverses the range expression and finds all nodes that are dynamically pointed to
    /// and returns it in a vector.
    fn dependent_on(&self) -> Vec<NodeIdx>;
    /// Traverses the range expression and updates stale pointers from older versions
    /// of a variable to a newer version.
    ///
    /// e.g.: `uint256 z = x + 100`, followed by `require(x < 100)`. Initially,
    /// without the `require` statement, `z`'s max is `2**256 - 1`, but with
    /// the introduction of the `require` statement, we do a little backtracking
    /// and can update `z`'s max to be `200`.
    fn update_deps(&mut self, mapping: &BTreeMap<NodeIdx, NodeIdx>);
    /// Attempts to replace range elements that form a cyclic dependency by replacing
    /// it with a new node. Ideally no cyclic dependencies occur in ranges as of now
    /// but in theory it can make sense.
    ///
    /// e.g.: take the basic expression `x + y`, in normal checked solidity math
    /// both x and y have the requirement `var <= 2**256 - 1 - other_var`, forming a
    /// cyclic dependency.
    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx);

    fn contains_op_set(
        &self,
        max: bool,
        op_set: &[RangeOp],
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError>;
}
