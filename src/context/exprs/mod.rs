use shared::analyzer::GraphError;
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

pub trait IntoExprErr<T> {
    fn into_expr_err(self, loc: Loc) -> Result<T, ExprErr>;
}

impl<T> IntoExprErr<T> for Result<T, GraphError> {
    fn into_expr_err(self, loc: Loc) -> Result<T, ExprErr> {
        match self {
            Ok(v) => Ok(v),
            Err(e) => Err(ExprErr::from_graph_err(loc, e)),
        }
    }
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
    BadRange(Loc, String),
    ContractFunctionNotFound(Loc, String),
    MemberAccessNotFound(Loc, String),
    FunctionNotFound(Loc, String),

    NonStoragePush(Loc, String),
    IntrinsicNamedArgs(Loc, String),
    InvalidFunctionInput(Loc, String),
    GraphError(Loc, GraphError),
}

impl ExprErr {
    pub fn from_graph_err(loc: Loc, graph_err: GraphError) -> Self {
        Self::GraphError(loc, graph_err)
    }
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
            BadRange(loc, ..) => *loc,
            ContractFunctionNotFound(loc, ..) => *loc,
            MemberAccessNotFound(loc, ..) => *loc,
            FunctionNotFound(loc, ..) => *loc,
            NonStoragePush(loc, ..) => *loc,
            IntrinsicNamedArgs(loc, ..) => *loc,
            InvalidFunctionInput(loc, ..) => *loc,
            GraphError(loc, ..) => *loc,
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
            BadRange(_, msg, ..) => msg,
            ContractFunctionNotFound(_, msg, ..) => msg,
            MemberAccessNotFound(_, msg, ..) => msg,
            FunctionNotFound(_, msg, ..) => msg,
            NonStoragePush(_, msg, ..) => msg,
            IntrinsicNamedArgs(_, msg, ..) => msg,
            InvalidFunctionInput(_, msg, ..) => msg,
            GraphError(_loc, shared::analyzer::GraphError::NodeConfusion(msg), ..) => msg,
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
            BadRange(..) => "Expected a range for a variable but there was none",
            ContractFunctionNotFound(..) => "Contract function could not be Found",
            MemberAccessNotFound(..) => "Member element could not be found",
            FunctionNotFound(..) => "Function could not be found",
            NonStoragePush(..) => "Pushing on non-storage based array is unsupported",
            IntrinsicNamedArgs(..) => "Arguments in calls to intrinsic functions cannot be named",
            InvalidFunctionInput(..) => "Arguments to this function call do not match required types",
            GraphError(..) => "Graph IR Error: This is a bug. Please report it at https://github.com/nascentxyz/pyrometer",
        }
    }
}
