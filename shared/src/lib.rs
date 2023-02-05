use crate::{
    context::{ContextEdge, ContextVar, Context},
    nodes::{
        Concrete, Ty, Var, Field, Error,
        ErrorParam, Struct, Enum, FunctionReturn, FunctionParam,
        Function, Contract, VarType, DynBuiltin, Builtin,
    }
};
use petgraph::{graph::*};
use solang_parser::pt::Identifier;

pub mod nodes;
pub mod analyzer;
pub mod context;
pub mod range;

pub type NodeIdx = NodeIndex<usize>;
pub type EdgeIdx = EdgeIndex<usize>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Node {
    Context(Context),
    ContextVar(ContextVar),
    ContextFork,
    FunctionCall,
    Builtin(Builtin),
    DynBuiltin(DynBuiltin),
    VarType(VarType),
    SourceUnit(usize),
    SourceUnitPart(usize, usize),
    Contract(Contract),
    Function(Function),
    FunctionParam(FunctionParam),
    FunctionReturn(FunctionReturn),
    Struct(Struct),
    Enum(Enum),
    Error(Error),
    ErrorParam(ErrorParam),
    Field(Field),
    Var(Var),
    Ty(Ty),
    Unresolved(Identifier),
    Concrete(Concrete),
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Edge {
    Part,
    Context(ContextEdge),
    Contract,
    Field,
    Enum,
    Struct,
    Error,
    ErrorParam,
    Event,
    Var,
    Ty,
    Func,
    FunctionParam,
    FunctionReturn,
}