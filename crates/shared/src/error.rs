use crate::NodeIdx;
use solang_parser::pt::Loc;

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub enum RepresentationErr {
    Context(ContextReprErr),
    Variable(VarReprErr),
}

impl RepresentationErr {
    fn msg(&self) -> &str {
        match self {
            Self::Context(c) => c.msg(),
            Self::Variable(c) => c.msg(),
        }
    }
}

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub enum ContextReprErr {
    VarCacheErr(NodeIdx, Vec<NodeIdx>),
    VarInvariantErr(NodeIdx, Vec<RepresentationErr>),
}

impl ContextReprErr {
    fn msg(&self) -> &str {
        match self {
            Self::VarCacheErr(idx, nodes) => string_to_static_str(format!("context node {idx:?}: has a cache-edge mismatch: {nodes:?} are missing in either cache or edges")),
            Self::VarInvariantErr(idx, errs) => string_to_static_str(format!("context node {idx:?}: has variable invariant errors: {}", errs.iter().map(|e| e.msg()).collect::<Vec<_>>().join(",\n\t"))),
        }
    }
}

fn string_to_static_str(s: String) -> &'static str {
    Box::leak(s.into_boxed_str())
}

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub enum VarReprErr {
    Unresolved(NodeIdx),
    StructErr(NodeIdx, &'static str),
    ContractErr(NodeIdx, &'static str),
    EnumErr(NodeIdx, &'static str),
    TyErr(NodeIdx, &'static str),
    FuncErr(NodeIdx, &'static str),
    ArrayErr(NodeIdx, &'static str),
}

impl VarReprErr {
    fn msg(&self) -> &str {
        string_to_static_str(match self {
            Self::Unresolved(idx) => format!("context variable node {idx:?}: is unresolved"),
            Self::StructErr(idx, str) => format!("context variable node {idx:?}: {str}"),
            Self::ContractErr(idx, str) => format!("context variable node {idx:?}: {str}"),
            Self::EnumErr(idx, str) => format!("context variable node {idx:?}: {str}"),
            Self::TyErr(idx, str) => format!("context variable node {idx:?}: {str}"),
            Self::FuncErr(idx, str) => format!("context variable node {idx:?}: {str}"),
            Self::ArrayErr(idx, str) => format!("context variable node {idx:?}: {str}"),
        })
    }
}

impl From<VarReprErr> for RepresentationErr {
    fn from(vre: VarReprErr) -> Self {
        RepresentationErr::Variable(vre)
    }
}

impl From<ContextReprErr> for RepresentationErr {
    fn from(cre: ContextReprErr) -> Self {
        RepresentationErr::Context(cre)
    }
}

#[derive(Debug, Clone, Ord, Eq, PartialEq, PartialOrd)]
pub enum GraphError {
    /// The analyzer thought the node was suppose to be one type, but it was a different one
    NodeConfusion(String),
    /// Call depth limit reached
    MaxStackDepthReached(String),
    /// Fork width limit reached
    MaxStackWidthReached(String),
    /// Tried to set the subcontext of a context that already had a subcontext
    ChildRedefinition(String),
    /// Tried to update a variable that is in an old context
    VariableUpdateInOldContext(String),
    /// Variable is detached from all contexts
    DetachedVariable(String),
    /// Expected a single element, found multiple
    ExpectedSingle(String),
    /// Expected a vector with a certain number of elements, but it was a different number of elements
    StackLengthMismatch(String),
    /// A variable had a cyclic reference to another variable and we were unable to break the cycle
    UnbreakableRecursion(String),
    /// The analyzer thought the node was suppose to be one type, but it was a different one
    UnknownVariable(String),
}

impl std::fmt::Display for GraphError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for GraphError {}

/// Convert some error into an expression error by attaching a code source location
pub trait IntoExprErr<T> {
    /// Convert into a ExprErr
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

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
/// An error that arose from the analyzer when interpreting expressions and statements
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
    GraphError(Loc, GraphError),
    ReprError(Loc, RepresentationErr),
    TestError(Loc, String),
    Unresolved(Loc, String),
}

impl ExprErr {
    /// Convert from a graph error
    pub fn from_graph_err(loc: Loc, graph_err: GraphError) -> Self {
        // panic!("here");
        Self::GraphError(loc, graph_err)
    }

    pub fn from_repr_err(loc: Loc, repr_err: RepresentationErr) -> Self {
        Self::ReprError(loc, repr_err)
    }
}

impl ExprErr {
    /// Get the code source location of the error
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
            ReprError(loc, ..) => *loc,
            TestError(loc, ..) => *loc,
        }
    }

    /// Get the error message
    pub fn msg(&self) -> &str {
        match self {
            ExprErr::ParseError(_, msg, ..) => msg,
            ExprErr::NoLhs(_, msg, ..) => msg,
            ExprErr::NoRhs(_, msg, ..) => msg,
            ExprErr::NoReturn(_, msg, ..) => msg,
            ExprErr::ArrayTy(_, msg, ..) => msg,
            ExprErr::ArrayIndex(_, msg, ..) => msg,
            ExprErr::UnhandledCombo(_, msg, ..) => msg,
            ExprErr::UnhandledExprRet(_, msg, ..) => msg,
            ExprErr::MultiNot(_, msg, ..) => msg,
            ExprErr::VarBadType(_, msg, ..) => msg,
            ExprErr::Todo(_, msg, ..) => msg,
            ExprErr::FunctionCallBlockTodo(_, msg, ..) => msg,
            ExprErr::BadRange(_, msg, ..) => msg,
            ExprErr::ContractFunctionNotFound(_, msg, ..) => msg,
            ExprErr::MemberAccessNotFound(_, msg, ..) => msg,
            ExprErr::FunctionNotFound(_, msg, ..) => msg,
            ExprErr::NonStoragePush(_, msg, ..) => msg,
            ExprErr::IntrinsicNamedArgs(_, msg, ..) => msg,
            ExprErr::InvalidFunctionInput(_, msg, ..) => msg,
            ExprErr::TakeFromFork(_, msg, ..) => msg,
            ExprErr::Unresolved(_, msg, ..) => msg,
            ExprErr::TestError(_, msg) => msg,
            ExprErr::ReprError(_, RepresentationErr::Context(c)) => c.msg(),
            ExprErr::ReprError(_, RepresentationErr::Variable(v)) => v.msg(),
            ExprErr::GraphError(_, GraphError::NodeConfusion(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::MaxStackDepthReached(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::MaxStackWidthReached(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::ChildRedefinition(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::DetachedVariable(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::VariableUpdateInOldContext(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::ExpectedSingle(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::StackLengthMismatch(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::UnbreakableRecursion(msg), ..) => msg,
            ExprErr::GraphError(_, GraphError::UnknownVariable(msg), ..) => msg,
        }
    }

    /// Get the top-level report message
    pub fn report_msg(&self) -> &str {
        match self {
            ExprErr::ParseError(..) => "Could not parse this",
            ExprErr::NoLhs(..) => "No left-hand side passed to expression",
            ExprErr::NoRhs(..) => "No right-hand side passed to expression",
            ExprErr::NoReturn(..) => "No returned element from expression",
            ExprErr::ArrayTy(..) => "Unexpected type as array element",
            ExprErr::ArrayIndex(..) => "Unexpected type as array index",
            ExprErr::UnhandledCombo(..) => "Unhandled ExprRet variant combination",
            ExprErr::UnhandledExprRet(..) => "Unhandled ExprRet variant",
            ExprErr::MultiNot(..) => "Expected a single ExprRet in Not statement, got ExprRet::Multi",
            ExprErr::VarBadType(..) => "This type cannot be made into a variable",
            ExprErr::Todo(..) => "TODO",
            ExprErr::FunctionCallBlockTodo(..) => "TODO",
            ExprErr::Unresolved(..) => "Unresolved type: This is likely a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::BadRange(..) => "Expected a range for a variable but there was none",
            ExprErr::ContractFunctionNotFound(..) => "Contract function could not be Found",
            ExprErr::MemberAccessNotFound(..) => "Member element could not be found",
            ExprErr::FunctionNotFound(..) => "Function could not be found",
            ExprErr::NonStoragePush(..) => "Pushing on non-storage based array is unsupported",
            ExprErr::IntrinsicNamedArgs(..) => "Arguments in calls to intrinsic functions cannot be named",
            ExprErr::InvalidFunctionInput(..) => "Arguments to this function call do not match required types",
            ExprErr::TakeFromFork(..) => "IR Error: Tried to take from an child context that ended up forking",
            ExprErr::ReprError(..) => "Representation Error: This is a bug.",
            ExprErr::TestError(..) => "Test error.",
            ExprErr::GraphError(_, GraphError::NodeConfusion(_), ..) => "Graph IR Error: Node type confusion. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::MaxStackDepthReached(_), ..) => "Max call depth reached - either recursion or loop",
            ExprErr::GraphError(_, GraphError::MaxStackWidthReached(_), ..) => "TODO: Max fork width reached - Need to widen variables and remove contexts",
            ExprErr::GraphError(_, GraphError::ChildRedefinition(_), ..) => "Graph IR Error: Child redefintion. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::DetachedVariable(_), ..) => "Graph IR Error: Detached Variable. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::VariableUpdateInOldContext(_), ..) => "Graph IR Error: Variable update in an old context. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::ExpectedSingle(_), ..) => "Graph IR Error: Expecting single expression return, got multiple. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::StackLengthMismatch(_), ..) => "Graph IR Error: Expected a particular number of elements on the context stack but found a different amount. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::UnbreakableRecursion(_), ..) => "Graph IR Error: Unbreakable recursion in variable range. This is potentially a bug. Please report it at https://github.com/nascentxyz/pyrometer",
            ExprErr::GraphError(_, GraphError::UnknownVariable(_), ..) => "Graph IR Error: Unknown variable. This is potentially a bug, but more likely a variable name is mistyped.",
        }
    }
}

impl std::fmt::Display for ExprErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.report_msg(), self.msg())
    }
}

impl std::error::Error for ExprErr {}
