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
            Memcopy => "memcopy".to_string(),
            SetIndices => "set_indices".to_string(),
            GetIndex => "get_index".to_string(),
            GetLength => "get_length".to_string(),
            SetLength => "set_length".to_string(),
        }
    }
}
