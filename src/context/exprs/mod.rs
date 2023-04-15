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

impl ExprErr {
    pub fn loc(&self) -> Loc {
        use ExprErr::*;
        match self {
            ExpectedSingle(loc, ..) => *loc,
            ArrayTy(loc, ..) => *loc,
            ArrayIndex(loc, ..) => *loc,
            UnhandledCombo(loc, ..) => *loc,
            UnhandledExprRet(loc, ..) => *loc,
            MultiNot(loc, ..) => *loc,
            VarBadType(loc, ..) => *loc,
            Todo(loc, ..) => *loc,
            RequireBadRange(loc, ..) => *loc,
            ContractFunctionNotFound(loc, ..) => *loc,
            MemberAccessNotFound(loc, ..) => *loc,
            FunctionNotFound(loc, ..) => *loc,
            NonStoragePush(loc, ..) => *loc,
            IntrinsicNamedArgs(loc, ..) => *loc,
        }
    }

    pub fn msg(&self) -> &str {
        use ExprErr::*;
        match self {
            ExpectedSingle(_, msg, ..) => msg,
            ArrayTy(_, msg, ..) => msg,
            ArrayIndex(_, msg, ..) => msg,
            UnhandledCombo(_, msg, ..) => msg,
            UnhandledExprRet(_, msg, ..) => msg,
            MultiNot(_, msg, ..) => msg,
            VarBadType(_, msg, ..) => msg,
            Todo(_, msg, ..) => msg,
            RequireBadRange(_, msg, ..) => msg,
            ContractFunctionNotFound(_, msg, ..) => msg,
            MemberAccessNotFound(_, msg, ..) => msg,
            FunctionNotFound(_, msg, ..) => msg,
            NonStoragePush(_, msg, ..) => msg,
            IntrinsicNamedArgs(_, msg, ..) => msg,
        }
    }

    pub fn report_msg(&self) -> &str {
        use ExprErr::*;
        match self {
            ExpectedSingle(..) => "Expected ExprRet::Single",
            ArrayTy(..) => "Unexpected type as array element",
            ArrayIndex(..) => "Unexpected type as array index",
            UnhandledCombo(..) => "Unhandled ExprRet variant combination",
            UnhandledExprRet(..) => "Unhandled ExprRet variant",
            MultiNot(..) => "Expected a single ExprRet in Not statement, got ExprRet::Multi",
            VarBadType(..) => "This type cannot be made into a variable",
            Todo(..) => "TODO",
            RequireBadRange(..) => "Expected a range for a variable but there was none",
            ContractFunctionNotFound(..) => "Contract function could not be Found",
            MemberAccessNotFound(..) => "Member element could not be found",
            FunctionNotFound(..) => "Function could not be found",
            NonStoragePush(..) => "Pushing on non-storage based array is unsupported",
            IntrinsicNamedArgs(..) => "Arguments in calls to intrinsic functions cannot be named",
        }
    }
}
