#![allow(clippy::too_many_arguments)]

mod array;
mod assign;
mod bin_op;
mod cmp;
mod cond_op;
mod context_builder;
mod env;
mod error;
mod func_call;
mod list;
mod literal;
mod loops;
mod member_access;
mod pre_post_in_decrement;
mod require;
mod variable;
pub mod yul;

pub use array::*;
pub use assign::*;
pub use bin_op::*;
pub use cmp::*;
pub use cond_op::*;
pub use context_builder::*;
pub use env::*;
pub use error::*;
pub use func_call::*;
pub use list::*;
pub use literal::*;
pub use loops::*;
pub use member_access::*;
pub use pre_post_in_decrement::*;
pub use require::*;
pub use variable::*;

/// Supertrait for parsing expressions
pub trait ExprTyParser:
    BinOp
    + Require
    + Variable
    + Literal
    + Array
    + MemberAccess
    + Cmp
    + CondOp
    + List
    + Env
    + PrePostIncDecrement
    + Assign
{
}
impl<T> ExprTyParser for T where
    T: BinOp
        + Require
        + Variable
        + Literal
        + Array
        + MemberAccess
        + Cmp
        + CondOp
        + List
        + Env
        + PrePostIncDecrement
        + Assign
{
}
