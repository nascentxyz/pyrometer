mod concrete;
mod elem_enum;
mod elem_trait;
mod expr;
mod map_or_array;
mod reference;

pub use concrete::*;
pub use elem_enum::*;
pub use elem_trait::*;
pub use expr::*;
pub use map_or_array::*;
pub use reference::*;
use shared::FlatExpr;

use std::fmt;

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum MinMaxed<T> {
    Minimized(Box<Elem<T>>),
    Maximized(Box<Elem<T>>),
}

impl<T> MinMaxed<T> {
    pub fn maxed(self) -> Elem<T> {
        match self {
            Self::Maximized(t) => *t,
            _ => panic!("MinMaxed was min not max"),
        }
    }

    pub fn mined(self) -> Elem<T> {
        match self {
            Self::Minimized(t) => *t,
            _ => panic!("MinMaxed was max not min"),
        }
    }
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
    /// Bitwise shift left
    Shl,
    /// Bitwise shift right
    Shr,
    /// Logical AND
    And,
    /// Logical OR
    Or,
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
    Exp(bool),
    /// Concatenation
    Concat,
    /// Memcopy
    Memcopy,
    /// Set memory indices of a memory object
    SetIndices,
    /// Gets an index of a memory object
    GetIndex,
    /// Set length of a memory object
    SetLength,
    /// Get Length of a memory object
    GetLength,
    /// Slice a memory object
    Slice,
}

impl TryFrom<FlatExpr> for RangeOp {
    type Error = ();
    fn try_from(flat: FlatExpr) -> Result<Self, ()> {
        use FlatExpr::*;
        let res = match flat {
            Power(_, unchecked) => RangeOp::Exp(unchecked),
            Multiply(_, unchecked) => RangeOp::Mul(unchecked),
            Add(_, unchecked) => RangeOp::Add(unchecked),
            Subtract(_, unchecked) => RangeOp::Sub(unchecked),
            Divide(_, unchecked) => RangeOp::Div(unchecked),
            Modulo(_) => RangeOp::Mod,
            AssignMultiply(_, unchecked) => RangeOp::Mul(unchecked),
            AssignAdd(_, unchecked) => RangeOp::Add(unchecked),
            AssignSubtract(_, unchecked) => RangeOp::Sub(unchecked),
            AssignDivide(_, unchecked) => RangeOp::Div(unchecked),
            AssignModulo(_) => RangeOp::Mod,
            ShiftLeft(_) => RangeOp::Shl,
            ShiftRight(_) => RangeOp::Shr,
            AssignShiftLeft(_) => RangeOp::Shl,
            AssignShiftRight(_) => RangeOp::Shr,
            BitwiseAnd(_) => RangeOp::BitAnd,
            AssignAnd(_) => RangeOp::BitAnd,
            BitwiseXor(_) => RangeOp::BitXor,
            AssignXor(_) => RangeOp::BitXor,
            BitwiseOr(_) => RangeOp::BitOr,
            AssignOr(_) => RangeOp::BitOr,
            BitwiseNot(_) => RangeOp::BitNot,
            _ => return Err(()),
        };
        Ok(res)
    }
}

impl RangeOp {
    pub fn commutative(&self) -> bool {
        use RangeOp::*;
        match self {
            Add(_i) => true,
            Mul(_i) => true,
            Sub(_i) => false,
            Div(_i) => false,
            Mod => false,
            Exp(_i) => false,
            Min => true,
            Max => true,

            Eq => true,
            Neq => true,
            Lt => false,
            Lte => false,
            Gt => false,
            Gte => false,
            And => true,
            Or => true,

            BitNot => false,
            BitAnd => false,
            BitXor => false,
            BitOr => false,
            Shl => false,
            Shr => false,

            Cast => false,

            SetLength => false,
            Memcopy => false,
            GetLength => false,
            SetIndices => false,
            GetIndex => false,
            Concat => false,
            Slice => false,
        }
    }

    pub fn non_commutative_logical_inverse(&self) -> Option<Self> {
        use RangeOp::*;
        match self {
            Lt => Some(Gt),
            Lte => Some(Gte),
            Gt => Some(Lt),
            Gte => Some(Lte),
            _ => None,
        }
    }

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

    pub fn require_rhs(self) -> Option<Self> {
        use RangeOp::*;
        let t = match self {
            Eq => Eq,
            Neq => Neq,
            Lte => Gte,
            Gte => Lte,
            Gt => Lt,
            Lt => Gt,
            other => {
                tracing::trace!("Require rhs other: {other:?}");
                return None;
            }
        };
        Some(t)
    }
}

impl fmt::Display for RangeOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RangeOp::*;
        match self {
            Add(..) => write!(f, "+"),
            Mul(..) => write!(f, "*"),
            Sub(..) => write!(f, "-"),
            Div(..) => write!(f, "/"),
            Shl => write!(f, "<<"),
            Shr => write!(f, ">>"),
            Mod => write!(f, "%"),
            Exp(_) => write!(f, "**"),
            Min => write!(f, "min"),
            Max => write!(f, "max"),
            Lt => write!(f, "<"),
            Gt => write!(f, ">"),
            Lte => write!(f, "<="),
            Gte => write!(f, ">="),
            Eq => write!(f, "=="),
            Neq => write!(f, "!="),
            And => write!(f, "&&"),
            Or => write!(f, "||"),
            Cast => write!(f, "cast"),
            BitAnd => write!(f, "&"),
            BitOr => write!(f, "|"),
            BitXor => write!(f, "^"),
            BitNot => write!(f, "~"),
            Concat => write!(f, "concat"),
            Memcopy => write!(f, "memcopy"),
            SetIndices => write!(f, "set_indices"),
            GetIndex => write!(f, "get_index"),
            GetLength => write!(f, "get_length"),
            SetLength => write!(f, "set_length"),
            Slice => write!(f, "slice"),
        }
    }
}
