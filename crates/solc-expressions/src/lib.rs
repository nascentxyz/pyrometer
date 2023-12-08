use solang_parser::pt::Loc;

mod array;
mod bin_op;
mod cmp;
mod cond_op;
mod context_builder;
mod env;
mod func_call;
mod list;
mod literal;
mod loops;
mod member_access;
mod require;
mod variable;
mod yul;

pub use array::*;
pub use bin_op::*;
pub use cmp::*;
pub use cond_op::*;
pub use context_builder::*;
pub use func_call::*;
pub use env::*;
pub use list::*;
pub use literal::*;
pub use loops::*;
pub use member_access::*;
pub use require::*;
pub use variable::*;
pub use yul::*;

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

impl<T> IntoExprErr<T> for Result<T, graph::GraphError> {
    fn into_expr_err(self, loc: Loc) -> Result<T, ExprErr> {
        match self {
            Ok(v) => Ok(v),
            Err(e) => Err(ExprErr::from_graph_err(loc, e)),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub enum ExprErr {
    ParseError(Loc, String),
    NoLhs(Loc, String),
    NoRhs(Loc, String),
    NoReturn(Loc, String),
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

    FunctionCallBlockTodo(Loc, String),

    NonStoragePush(Loc, String),
    IntrinsicNamedArgs(Loc, String),
    InvalidFunctionInput(Loc, String),
    TakeFromFork(Loc, String),
    GraphError(Loc, graph::GraphError),
    Unresolved(Loc, String),
}

impl ExprErr {
    pub fn from_graph_err(loc: Loc, graph_err: graph::GraphError) -> Self {
        Self::GraphError(loc, graph_err)
    }
}

impl ExprErr {
    pub fn loc(&self) -> Loc {
        use ExprErr::*;
        match self {
            ParseError(loc, ..) => *loc,
            NoLhs(loc, ..) => *loc,
            NoRhs(loc, ..) => *loc,
            NoReturn(loc, ..) => *loc,
            ArrayTy(loc, ..) => *loc,
            ArrayIndex(loc, ..) => *loc,
            UnhandledCombo(loc, ..) => *loc,
            UnhandledExprRet(loc, ..) => *loc,
            MultiNot(loc, ..) => *loc,
            VarBadType(loc, ..) => *loc,
            Todo(loc, ..) => *loc,
            FunctionCallBlockTodo(loc, ..) => *loc,
            BadRange(loc, ..) => *loc,
            ContractFunctionNotFound(loc, ..) => *loc,
            MemberAccessNotFound(loc, ..) => *loc,
            FunctionNotFound(loc, ..) => *loc,
            NonStoragePush(loc, ..) => *loc,
            IntrinsicNamedArgs(loc, ..) => *loc,
            InvalidFunctionInput(loc, ..) => *loc,
            TakeFromFork(loc, ..) => *loc,
            GraphError(loc, ..) => *loc,
            Unresolved(loc, ..) => *loc,
        }
    }

    pub fn msg(&self) -> &str {
        use ExprErr::*;
        match self {
            ParseError(_, msg, ..) => msg,
            NoLhs(_, msg, ..) => msg,
            NoRhs(_, msg, ..) => msg,
            NoReturn(_, msg, ..) => msg,
            ArrayTy(_, msg, ..) => msg,
            ArrayIndex(_, msg, ..) => msg,
            UnhandledCombo(_, msg, ..) => msg,
            UnhandledExprRet(_, msg, ..) => msg,
            MultiNot(_, msg, ..) => msg,
            VarBadType(_, msg, ..) => msg,
            Todo(_, msg, ..) => msg,
            FunctionCallBlockTodo(_, msg, ..) => msg,
            BadRange(_, msg, ..) => msg,
            ContractFunctionNotFound(_, msg, ..) => msg,
            MemberAccessNotFound(_, msg, ..) => msg,
            FunctionNotFound(_, msg, ..) => msg,
            NonStoragePush(_, msg, ..) => msg,
            IntrinsicNamedArgs(_, msg, ..) => msg,
            InvalidFunctionInput(_, msg, ..) => msg,
            TakeFromFork(_, msg, ..) => msg,
            Unresolved(_, msg, ..) => msg,
            GraphError(_loc, graph::GraphError::NodeConfusion(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::MaxStackDepthReached(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::MaxStackWidthReached(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::ChildRedefinition(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::DetachedVariable(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::VariableUpdateInOldContext(msg), ..) => {
                msg
            }
            GraphError(_loc, graph::GraphError::ExpectedSingle(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::StackLengthMismatch(msg), ..) => msg,
            GraphError(_loc, graph::GraphError::UnbreakableRecursion(msg), ..) => msg,
        }
    }

    pub fn report_msg(&self) -> &str {
        use ExprErr::*;
        match self {
            ParseError(..) => "Could not parse this",
            NoLhs(..) => "No left-hand side passed to expression",
            NoRhs(..) => "No right-hand side passed to expression",
            NoReturn(..) => "No returned element from expression",
            ArrayTy(..) => "Unexpected type as array element",
            ArrayIndex(..) => "Unexpected type as array index",
            UnhandledCombo(..) => "Unhandled ExprRet variant combination",
            UnhandledExprRet(..) => "Unhandled ExprRet variant",
            MultiNot(..) => "Expected a single ExprRet in Not statement, got ExprRet::Multi",
            VarBadType(..) => "This type cannot be made into a variable",
            Todo(..) => "TODO",
            FunctionCallBlockTodo(..) => "TODO",
            Unresolved(..) => "Unresolved type: This is likely a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            BadRange(..) => "Expected a range for a variable but there was none",
            ContractFunctionNotFound(..) => "Contract function could not be Found",
            MemberAccessNotFound(..) => "Member element could not be found",
            FunctionNotFound(..) => "Function could not be found",
            NonStoragePush(..) => "Pushing on non-storage based array is unsupported",
            IntrinsicNamedArgs(..) => "Arguments in calls to intrinsic functions cannot be named",
            InvalidFunctionInput(..) => "Arguments to this function call do not match required types",
            TakeFromFork(..) => "IR Error: Tried to take from an child context that ended up forking",
            GraphError(_loc, graph::GraphError::NodeConfusion(_), ..) => "Graph IR Error: Node type confusion. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::MaxStackDepthReached(_), ..) => "Max call depth reached - either recursion or loop",
            GraphError(_loc, graph::GraphError::MaxStackWidthReached(_), ..) => "TODO: Max fork width reached - Need to widen variables and remove contexts",
            GraphError(_loc, graph::GraphError::ChildRedefinition(_), ..) => "Graph IR Error: Child redefintion. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::DetachedVariable(_), ..) => "Graph IR Error: Detached Variable. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::VariableUpdateInOldContext(_), ..) => "Graph IR Error: Variable update in an old context. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::ExpectedSingle(_), ..) => "Graph IR Error: Expecting single expression return, got multiple. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::StackLengthMismatch(_), ..) => "Graph IR Error: Expected a particular number of elements on the context stack but found a different amount. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            GraphError(_loc, graph::GraphError::UnbreakableRecursion(_), ..) => "Graph IR Error: Unbreakable recursion in variable range. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
        }
    }
}
