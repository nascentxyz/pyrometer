use crate::NodeIdx;
use crate::GraphLike;
use std::collections::BTreeMap;
use crate::context::ContextVarNode;
use crate::range::elem_ty::RangeExpr;
use crate::range::elem_ty::Elem;

/// An operation to be performed on a range element
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RangeOp {
    /// Addition
    Add,
    /// Multiplication
    Mul,
    /// Subtraction
    Sub,
    /// Division
    Div,
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
    /// Exponentiation
    Exp,
}


impl RangeOp {
    /// Attempts to return the inverse range operation (e.g.: `RangeOp::Add => RangeOp::Sub`)
    pub fn inverse(self) -> Option<Self> {
        use RangeOp::*;
        match self {
            Add => Some(Sub),
            Mul => Some(Div),
            Sub => Some(Add),
            Div => Some(Mul),
            Shl => Some(Shr),
            Shr => Some(Shl),
            Eq => Some(Neq),
            Neq => Some(Eq),
            _ => None
            // e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }
}

impl ToString for RangeOp {
    fn to_string(&self) -> String {
        use RangeOp::*;
        match self {
            Add => "+".to_string(),
            Mul => "*".to_string(),
            Sub => "-".to_string(),
            Div => "/".to_string(),
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
        }
    }
}


pub trait RangeElem<T> {
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its maximum value
    fn maximize(&self, analyzer: &impl GraphLike) -> Elem<T>;
    /// Tries to evaluate a range element down to a concrete or maximally simplified expression to its minimum value
    fn minimize(&self, analyzer: &impl GraphLike) -> Elem<T>;
    /// Tries to simplify to maximum(i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Elem<T>;
    /// Tries to simplify to minimum (i.e.: leaves symbolic/dynamic values as they are)
    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Elem<T>;
    /// Checks if two range elements are equal
    fn range_eq(&self, other: &Self) -> bool;
    /// Tries to compare the ordering of two range elements
    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering>;
    /// Constructs a range `Elem::Expr` given a lhs, rhs, and operation ([`RangeOp`]).
    fn range_op(lhs: Elem<T>, rhs: Elem<T>, op: RangeOp) -> Elem<T> where Self: Sized {
        Elem::Expr(RangeExpr::new(lhs, op, rhs))
    }
    /// Traverses the range expression and finds all nodes that are dynamically pointed to
    /// and returns it in a vector.
    fn dependent_on(&self) -> Vec<ContextVarNode>;
    /// Traverses the range expression and updates stale pointers from older versions
    /// of a variable to a newer version.
    ///
    /// e.g.: `uint256 z = x + 100`, followed by `require(x < 100)`. Initially,
    /// without the `require` statement, `z`'s max is `2**256 - 1`, but with
    /// the introduction of the `require` statement, we do a little backtracking
    /// and can update `z`'s max to be `200`.
    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>);
    /// Attempts to replace range elements that form a cyclic dependency by replacing
    /// it with a new node. Ideally no cyclic dependencies occur in ranges as of now
    /// but in theory it can make sense.
    ///
    /// e.g.: take the basic expression `x + y`, in normal checked solidity math
    /// both x and y have the requirement `var <= 2**256 - 1 - other_var`, forming a
    /// cyclic dependency.
    fn filter_recursion(&mut self, node_idx: NodeIdx, old: Elem<T>);
}


