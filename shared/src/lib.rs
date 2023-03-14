use std::collections::HashMap;
use crate::analyzer::GraphLike;
use crate::context::ContextVarNode;

use crate::context::ContextNode;

use crate::analyzer::AsDotStr;
use crate::analyzer::AnalyzerLike;
use crate::{
    context::{ContextEdge, ContextVar, Context},
    nodes::*
};
use petgraph::{graph::*};
use solang_parser::pt::Identifier;
use lazy_static::lazy_static;

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
    Msg(Msg),
    Block(Block),
}


pub fn as_dot_str(idx: NodeIdx, analyzer: &impl GraphLike) -> String {
    use crate::Node::*;
    match analyzer.node(idx) {
        Context(_) => ContextNode::from(idx).as_string(),
        ContextVar(_) => ContextVarNode::from(idx).as_dot_str(analyzer),
        ContextFork => "Context Fork".to_string(),
        FunctionCall => "Function Call".to_string(),
        Builtin(bi) => bi.as_string(analyzer),
        VarType(v_ty) => v_ty.as_dot_str(analyzer), 
        Contract(_c) => ContractNode::from(idx).as_dot_str(analyzer),
        Function(_f) => FunctionNode::from(idx).as_dot_str(analyzer),
        FunctionParam(_fp) => FunctionParamNode::from(idx).as_dot_str(analyzer),
        FunctionReturn(_fr) => FunctionReturnNode::from(idx).as_dot_str(analyzer),
        Struct(_s) => StructNode::from(idx).as_dot_str(analyzer),
        Enum(_e) => EnumNode::from(idx).as_dot_str(analyzer),
        Field(_f) => FieldNode::from(idx).as_dot_str(analyzer),
        Var(_v) => VarNode::from(idx).as_dot_str(analyzer),
        Ty(_t) => TyNode::from(idx).as_dot_str(analyzer),
        // Concrete(c) => c.as_human_string(),
        e => format!("{:?}", e)
    }
}

impl Node {
    pub fn dot_str_color(&self) -> String {
        use crate::Node::*;
        let c = match self {
            Context(_) => TOKYO_NIGHT_COLORS.get("purple").unwrap(),
            ContextVar(_) => TOKYO_NIGHT_COLORS.get("orange").unwrap(),
            FunctionCall => TOKYO_NIGHT_COLORS.get("cyan").unwrap(),
            Contract(_c) => TOKYO_NIGHT_COLORS.get("green").unwrap(),
            Function(_f) => TOKYO_NIGHT_COLORS.get("cyan").unwrap(),
            Struct(_s) => TOKYO_NIGHT_COLORS.get("yellow").unwrap(),
            Enum(_e) => TOKYO_NIGHT_COLORS.get("yellow").unwrap(),
            _ => TOKYO_NIGHT_COLORS.get("default").unwrap()
        };
        c.to_string()
    }
}

lazy_static! {
    pub static ref TOKYO_NIGHT_COLORS: HashMap<&'static str, &'static str> = {
        let mut m = HashMap::new();
        m.insert("red", "#f7768e");
        m.insert("orange", "#ff9e64");
        m.insert("yellow", "#e0af68");
        m.insert("green", "#9ece6a");
        m.insert("cyan", "#73daca");
        m.insert("teal", "#2ac3de");
        m.insert("darkblue", "#7aa2f7");
        m.insert("purple", "#bb9af7");
        m.insert("bg", "#1a1b26");
        m.insert("font", "#c0caf5");
        m.insert("deepred", "#703440");
        m.insert("default", "#565f89");
        m
    };
}


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Edge {
    Part,
    Context(ContextEdge),
    Contract,
    InheritedContract,
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
    FuncModifier(usize),
    Modifier,
    FallbackFunc,
    Constructor,
    ReceiveFunc,
}