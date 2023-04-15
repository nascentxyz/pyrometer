use solang_parser::pt::Loc;

mod array;
mod bin_op;
mod cmp;
mod cond_op;
mod env;
mod list;
mod literal;
mod member_access;
mod require;
mod variable;

pub use array::*;
pub use bin_op::*;
pub use cmp::*;
pub use cond_op::*;
pub use env::*;
pub use list::*;
pub use literal::*;
pub use member_access::*;
pub use require::*;
pub use variable::*;

pub trait ExprParser:
    BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List + Env
{
}
impl<T> ExprParser for T where
    T: BinOp + Require + Variable + Literal + Array + MemberAccess + Cmp + CondOp + List + Env
{
}

#[derive(Debug, Clone)]
pub enum ExprErr {
    ExpectedSingle(Loc, String),
    ArrayTy(Loc, String),
    ArrayIndex(Loc, String),
    UnhandledCombo(Loc, String),
    UnhandledExprRet(Loc, String),
    MultiNot(Loc, String),
    VarBadType(Loc, String),
    Todo(Loc, String),
    RequireBadRange(Loc, String),
    ContractFunctionNotFound(Loc, String),
    MemberAccessNotFound(Loc, String),
    FunctionNotFound(Loc, String),

    NonStoragePush(Loc, String),
    IntrinsicNamedArgs(Loc, String),
}
