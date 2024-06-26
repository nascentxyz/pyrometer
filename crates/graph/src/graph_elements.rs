use crate::elem::Elem;
use crate::{nodes::*, VarType};

use shared::{AnalyzerLike, GraphDot, GraphLike, Heirarchical, NodeIdx, RangeArena};

use lazy_static::lazy_static;
use petgraph::{Directed, Graph};
use solang_parser::pt::{Identifier, Loc};

use std::collections::HashMap;

pub trait GraphBackend:
    GraphLike<Edge = Edge, Node = Node, RangeElem = Elem<Concrete>> + GraphDot
{
}
pub trait AnalyzerBackend:
    AnalyzerLike<
        Builtin = Builtin,
        MsgNode = MsgNode,
        BlockNode = BlockNode,
        FunctionNode = FunctionNode,
        FunctionParam = FunctionParam,
        FunctionReturn = FunctionReturn,
        Function = Function,
    > + GraphBackend
{
    fn add_concrete_var(
        &mut self,
        ctx: ContextNode,
        concrete: Concrete,
        loc: Loc,
    ) -> Result<ContextVarNode, Self::ExprErr>;
}

pub trait AsDotStr {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String;
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Node {
    /// An analyzed function body/context
    Context(Context),
    /// A variable attached to a context or the previous version of this variable (akin to SSA form)
    ContextVar(ContextVar),
    /// A fork in execution caused by an if-like statement
    ContextFork,
    /// A call to another function, either public or internal
    FunctionCall,
    /// A builtin solidity type (i.e. Address, Uint, Bytes, etc)
    Builtin(Builtin),
    /// A node that represents whether a variable's type is a User-defined type, builtin type or a concrete
    VarType(VarType),
    /// The entry node in the graph
    Entry,
    /// A source unit (i.e. a source file)
    SourceUnit(SourceUnit),
    /// A subcomponent of the source unit
    SourceUnitPart(SourceUnitPart),
    /// A contract
    Contract(Contract),
    /// A solidity-based function
    Function(Function),
    /// A solidity-based function parameter
    FunctionParam(FunctionParam),
    /// A solidity-based function return parameter
    FunctionReturn(FunctionReturn),
    /// A solidity-based struct
    Struct(Struct),
    /// A solidity-based enum
    Enum(Enum),
    /// A solidity-based error
    Error(Error),
    /// A solidity-based error parameter
    ErrorParam(ErrorParam),
    /// A solidity-based struct or contract field
    Field(Field),
    /// A storage or constant variable on a contract
    Var(Var),
    /// A solidity-based type alias
    Ty(Ty),
    /// An unresolved type
    Unresolved(Identifier),
    /// A concrete value (i.e. '1' or '0x111')
    Concrete(Concrete),
    /// The `msg` global in solidity
    Msg(Msg),
    /// The `block` global in solidity
    Block(Block),
}

pub fn as_dot_str(
    idx: NodeIdx,
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> String {
    use crate::Node::*;
    match analyzer.node(idx) {
        Context(_) => ContextNode::from(idx).as_dot_str(analyzer, arena),
        ContextVar(_) => ContextVarNode::from(idx).as_dot_str(analyzer, arena),
        ContextFork => "Context Fork".to_string(),
        FunctionCall => "Function Call".to_string(),
        Builtin(bi) => bi.as_string(analyzer).unwrap(),
        VarType(v_ty) => v_ty.as_string(analyzer).unwrap(),
        Contract(_c) => ContractNode::from(idx).as_dot_str(analyzer, arena),
        Function(_f) => FunctionNode::from(idx).as_dot_str(analyzer, arena),
        FunctionParam(_fp) => FunctionParamNode::from(idx).as_dot_str(analyzer, arena),
        FunctionReturn(_fr) => FunctionReturnNode::from(idx).as_dot_str(analyzer, arena),
        Struct(_s) => StructNode::from(idx).as_dot_str(analyzer, arena),
        Enum(_e) => EnumNode::from(idx).as_dot_str(analyzer, arena),
        Field(_f) => FieldNode::from(idx).as_dot_str(analyzer, arena),
        Var(_v) => VarNode::from(idx).as_dot_str(analyzer, arena),
        Ty(_t) => TyNode::from(idx).as_dot_str(analyzer, arena),
        // Concrete(c) => c.as_human_string(),
        e => format!("{e:?}"),
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
            _ => TOKYO_NIGHT_COLORS.get("default").unwrap(),
        };
        c.to_string()
    }
}

pub fn num_to_color(x: usize) -> String {
    let c = match x % 29 {
        0 => TOKYO_NIGHT_COLORS.get("default").unwrap(),
        1 => TOKYO_NIGHT_COLORS.get("font").unwrap(),
        2 => TOKYO_NIGHT_COLORS.get("bg_highlight").unwrap(),
        3 => TOKYO_NIGHT_COLORS.get("terminal_black").unwrap(),
        4 => TOKYO_NIGHT_COLORS.get("fg_dark").unwrap(),
        5 => TOKYO_NIGHT_COLORS.get("fg_gutter").unwrap(),
        6 => TOKYO_NIGHT_COLORS.get("dark3").unwrap(),
        7 => TOKYO_NIGHT_COLORS.get("dark5").unwrap(),
        8 => TOKYO_NIGHT_COLORS.get("blue0").unwrap(),
        9 => TOKYO_NIGHT_COLORS.get("cyan").unwrap(),
        10 => TOKYO_NIGHT_COLORS.get("blue2").unwrap(),
        11 => TOKYO_NIGHT_COLORS.get("blue5").unwrap(),
        12 => TOKYO_NIGHT_COLORS.get("blue6").unwrap(),
        13 => TOKYO_NIGHT_COLORS.get("blue7").unwrap(),
        14 => TOKYO_NIGHT_COLORS.get("magenta2").unwrap(),
        15 => TOKYO_NIGHT_COLORS.get("purple").unwrap(),
        16 => TOKYO_NIGHT_COLORS.get("orange").unwrap(),
        17 => TOKYO_NIGHT_COLORS.get("yellow").unwrap(),
        18 => TOKYO_NIGHT_COLORS.get("green").unwrap(),
        19 => TOKYO_NIGHT_COLORS.get("green1").unwrap(),
        20 => TOKYO_NIGHT_COLORS.get("teal").unwrap(),
        21 => TOKYO_NIGHT_COLORS.get("red").unwrap(),
        22 => TOKYO_NIGHT_COLORS.get("red1").unwrap(),
        23 => TOKYO_NIGHT_COLORS.get("cyan").unwrap(),
        24 => TOKYO_NIGHT_COLORS.get("teal").unwrap(),
        25 => TOKYO_NIGHT_COLORS.get("darkblue").unwrap(),
        26 => TOKYO_NIGHT_COLORS.get("purple").unwrap(),
        27 => TOKYO_NIGHT_COLORS.get("bg1").unwrap(),
        28 => TOKYO_NIGHT_COLORS.get("deepred").unwrap(),
        _ => unreachable!(),
    };
    c.to_string()
}

lazy_static! {
    pub static ref TOKYO_NIGHT_COLORS: HashMap<&'static str, &'static str> = {
        let mut m = HashMap::new();
        m.insert("bg_dark", "#1f2335");
        m.insert("bg1", "#24283b");
        m.insert("bg_highlight", "#292e42");
        m.insert("terminal_black", "#414868");
        m.insert("fg_dark", "#a9b1d6");
        m.insert("fg_gutter", "#3b4261");
        m.insert("dark3", "#545c7e");
        m.insert("dark5", "#737aa2");
        m.insert("blue0", "#3d59a1");
        m.insert("cyan", "#7dcfff");
        m.insert("blue2", "#0db9d7");
        m.insert("blue5", "#89ddff");
        m.insert("blue6", "#b4f9f8");
        m.insert("blue7", "#394b70");
        m.insert("magenta2", "#ff007c");
        m.insert("purple", "#9d7cd8");
        m.insert("orange", "#ff9e64");
        m.insert("yellow", "#e0af68");
        m.insert("green", "#9ece6a");
        m.insert("green1", "#41a6b5");
        m.insert("teal", "#1abc9c");
        m.insert("red", "#f7768e");
        m.insert("red1", "#db4b4b");
        m.insert("cyan", "#73daca");
        m.insert("teal", "#2ac3de");
        m.insert("darkblue", "#7aa2f7");
        m.insert("purple", "#bb9af7");
        m.insert("bg", "#1a1b26");
        m.insert("font", "#c0caf5");
        m.insert("deepred", "#703440");
        m.insert("deeporange", "#b5683c");
        m.insert("default", "#565f89");
        m
    };
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Edge {
    /// A connection between a Source and the Entry
    Source,
    /// A connection between a SourceUnitPart and a Source
    Part,
    /// An edge indicating that a source or contract was imported
    Import,
    /// An edge that contains a subtype of edge corresponding to some
    /// kind of context-based relationship
    Context(ContextEdge),
    /// A connection for a contract to it's parent
    Contract,
    /// A connection for a contract to it's parent contract
    InheritedContract,
    /// A connection for a field to it's parent
    Field,
    /// A connection for an enum to it's parent
    Enum,
    /// A connection for a struct to it's parent
    Struct,
    /// A connection for an error to it's parent
    Error,
    /// A connection for an error parameter to it's parent error
    ErrorParam,
    /// A connection for an event to it's parent
    Event,
    /// A connection for a storage/constant variable to it's parent
    Var,
    Ty,
    /// A connection for a function to it's parent
    Func,
    /// A connection for a function parameter to it's parent function
    FunctionParam,
    /// A connection for a function return to it's parent function
    FunctionReturn,
    /// A connection for a function modifier to it's parent function, with its order
    FuncModifier(usize),
    /// A connection for a modifier to it's parent
    Modifier,
    /// A connection for a fallback function to it's parent contract
    FallbackFunc,
    /// A connection for a contract constructor function to it's parent contract
    Constructor,
    /// A connection for a receive function to it's parent contract
    ReceiveFunc,
    /// A connection for a library-based function to a contract
    LibraryFunction(NodeIdx),
    /// A connection for a builtin function
    BuiltinFunction,
}

impl Heirarchical for Edge {
    fn heirarchical_num(&self) -> usize {
        use crate::Edge::*;
        match self {
            Source => 0,
            Part | Import => 1,

            Contract | Ty | Field | Enum | Struct | Error | Event | Var | InheritedContract
            | Modifier | FallbackFunc | Constructor | ReceiveFunc | LibraryFunction(_)
            | BuiltinFunction | Func => 2,

            Context(_) | ErrorParam | FunctionParam | FunctionReturn | FuncModifier(_) => 3,
        }
    }
}

/// An enum denoting either a call or a fork
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum CallFork {
    Call(ContextNode),
    Fork(ContextNode, ContextNode),
}

impl CallFork {
    pub fn maybe_call(&self) -> Option<ContextNode> {
        match self {
            CallFork::Call(c) => Some(*c),
            _ => None,
        }
    }

    pub fn maybe_fork(&self) -> Option<(ContextNode, ContextNode)> {
        match self {
            CallFork::Fork(w1, w2) => Some((*w1, *w2)),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum ContextEdge {
    // Control flow
    /// A connection for a context to a function
    Context,
    /// A connection for a subcontext to it's parent context
    Subcontext,
    /// A connection for a context to another context in which the source is the new
    /// context and the target is the original context. That is:
    /// ContextA -subcontext-> ContextB -subcontext> ContextAPrime
    ///    ^-----------------------ReturningContext--------|
    ReturningContext,
    /// A connection to a ContextFork to denote a fork in execution
    ContextFork,
    /// Currently unused
    ContextMerge,
    /// A call to a function, a connection from a context to a `FuncCall` node
    Call,
    /// A loop
    Loop,

    // Context Variables
    /// A new variable in cotext
    Variable,
    /// A connection between a variable in a new context and that variable in a parent context denoting
    /// that it is inherited from a parent scope
    InheritedVariable,
    /// A connection between a `Var` and a context variable denoting that the variable reads from storage
    InheritedStorageVariable,
    /// A connection to the calldata variable
    CalldataVariable,

    /// A connection between a variable and a parent variable where the child is some attribute on the parent
    /// (i.e. `.length`)
    AttrAccess(&'static str),
    /// A connection between a variable and the index that was used to create the variable from an IndexAccess
    Index,
    /// A connection between a variable and a parent variable where the child is some index into the parent
    /// (i.e. `x[1]`)
    IndexAccess,
    /// A connection between a variable and a parent variable where the child is some field of the parent
    StructAccess,
    /// A connection between a function-as-a-variable and the contract that holds that function
    FuncAccess,
    /// A write to a storage variable, connecting the variable that is written to the variable and the storage variable itself
    StorageWrite,
    /// An access to a storage slot
    SlotAccess,

    // Variable incoming edges
    /// Unused
    Assign,
    /// Unused
    StorageAssign,
    /// Unused
    MemoryAssign,
    /// A connection of a variable to the previous version of that variable
    Prev,

    // Control flow
    /// A connection between a variable and the context denoting that the variable is returned
    Return,
    /// A continuation of a context
    Continue(&'static str),
    /// A connection between a brand new created variable for a function's context and the variable
    InputVariable,
    /// A connection to a return variable that should be assigned
    ReturnAssign(bool),

    // Range analysis
    /// Unused
    Range,
}

#[derive(Default)]
pub(crate) struct DummyGraph {}

impl GraphLike for DummyGraph {
    type Node = Node;
    type Edge = Edge;
    type RangeElem = Elem<Concrete>;
    fn graph_mut(&mut self) -> &mut Graph<Node, Edge, Directed, usize> {
        panic!("Dummy Graph")
    }

    fn graph(&self) -> &Graph<Node, Edge, Directed, usize> {
        panic!("Dummy Graph")
    }
}

impl GraphBackend for DummyGraph {}
impl GraphDot for DummyGraph {
    type T = Elem<Concrete>;

    fn dot_str(&self, _arena: &mut RangeArena<<Self as GraphDot>::T>) -> String {
        // Provide a basic implementation or a placeholder
        "digraph DummyGraph {}".to_string()
    }

    fn cluster_str(
        &self,
        _arena: &mut RangeArena<Self::T>,
        _node: NodeIdx,
        _cluster_num: &mut usize,
        _is_killed: bool,
        _handled_nodes: std::sync::Arc<std::sync::Mutex<std::collections::BTreeSet<NodeIdx>>>,
        _handled_edges: std::sync::Arc<
            std::sync::Mutex<std::collections::BTreeSet<petgraph::prelude::EdgeIndex<usize>>>,
        >,
        _depth: usize,
        _as_mermaid: bool,
    ) -> Option<String>
    where
        Self: std::marker::Sized,
    {
        todo!()
    }

    fn dot_str_no_tmps(&self, _arena: &mut RangeArena<Self::T>) -> String
    where
        Self: std::marker::Sized,
    {
        todo!()
    }

    fn mermaid_str(&self, _arena: &mut RangeArena<Self::T>) -> String
    where
        Self: std::marker::Sized,
    {
        todo!()
    }
}
