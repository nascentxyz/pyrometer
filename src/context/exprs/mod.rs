mod array;
mod bin_op;
mod cmp;
mod literal;
mod member_access;
mod require;
mod variable;
mod cond_op;
mod list;

pub use array::*;
pub use bin_op::*;
pub use cmp::*;
pub use literal::*;
pub use member_access::*;
pub use require::*;
pub use variable::*;
pub use cond_op::*;
pub use list::*;

pub trait ExprParser: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List {}
impl<T> ExprParser for T where T: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List {}
