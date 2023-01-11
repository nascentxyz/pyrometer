mod array;
mod bin_op;
mod cmp;
mod literal;
mod member_access;
mod require;
mod variable;

pub use array::*;
pub use bin_op::*;
pub use cmp::*;
pub use literal::*;
pub use member_access::*;
pub use require::*;
pub use variable::*;

pub trait ExprParser: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp {}
impl<T> ExprParser for T where T: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp {}
