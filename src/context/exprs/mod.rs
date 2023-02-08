mod array;
mod bin_op;
mod cmp;
mod cond_op;
mod list;
mod literal;
mod member_access;
mod require;
mod variable;
mod env;

pub use array::*;
pub use bin_op::*;
pub use cmp::*;
pub use cond_op::*;
pub use list::*;
pub use literal::*;
pub use member_access::*;
pub use require::*;
pub use variable::*;
pub use env::*;

pub trait ExprParser:
    BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List + Env
{
}
impl<T> ExprParser for T where
    T: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List + Env
{
}
