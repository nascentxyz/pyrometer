//! Solidity and EVM specific representations as nodes in the graph
use solang_parser::pt::Expression;
use crate::GraphLike;
use crate::analyzer::AsDotStr;
use crate::context::ContextVarNode;
use crate::range::elem_ty::Elem;
use crate::range::elem::RangeElem;
use crate::range::SolcRange;
use crate::range::Range;
use crate::analyzer::AnalyzerLike;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::Type;

mod contract_ty;
pub use contract_ty::*;
mod enum_ty;
pub use enum_ty::*;
mod struct_ty;
pub use struct_ty::*;
mod func_ty;
pub use func_ty::*;
mod err_ty;
pub use err_ty::*;
mod var_ty;
pub use var_ty::*;
mod ty_ty;
pub use ty_ty::*;
mod concrete;
pub use concrete::*;
mod msg;
pub use msg::*;
mod block;
pub use block::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum VarType {
    User(TypeNode),
    BuiltIn(BuiltInNode, Option<SolcRange>),
    Array(DynBuiltInNode, Option<ContextVarNode>),
    Mapping(DynBuiltInNode),
    Concrete(ConcreteNode),
}

impl AsDotStr for VarType {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        self.as_string(analyzer)
    }
}

impl VarType {
    pub fn concrete_to_builtin(&mut self, analyzer: &mut impl AnalyzerLike) {
        if let VarType::Concrete(cnode) = self {
            let c = cnode.underlying(analyzer).clone();
            match c {
                crate::Concrete::Uint(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Uint(*size))),
                        SolcRange::from(c)
                    );
                    *self = new_ty;
                }
                crate::Concrete::Int(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Int(*size))),
                        SolcRange::from(c)
                    );
                    *self = new_ty;
                }
                crate::Concrete::Bool(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bool)),
                        SolcRange::from(c)
                    );
                    *self = new_ty;
                }
                crate::Concrete::Address(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Address)),
                        SolcRange::from(c)
                    );
                    *self = new_ty;
                }
                crate::Concrete::Bytes(ref s, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bytes(*s))),
                        SolcRange::from(c)
                    );
                    *self = new_ty;
                }
                // Concrete::Bytes(size, val) => ,
                // Concrete::Address(Address),
                // Concrete::DynBytes(Vec<u8>),
                // Concrete::Array(Vec<Concrete>),
                _ => {}
            }
        }
    }

    pub fn try_from_idx(analyzer: &(impl GraphLike + ?Sized), node: NodeIdx) -> Option<VarType> {
        // get node, check if typeable and convert idx into vartype
        match analyzer.node(node) {
            Node::VarType(a) => Some(a.clone()),
            Node::Builtin(b) => Some(VarType::BuiltIn(
                node.into(),
                SolcRange::try_from_builtin(b),
            )),
            Node::DynBuiltin(dyn_b) => match dyn_b {
                DynBuiltin::Array(_) => Some(VarType::Array(
                    node.into(),
                    None,
                )),
                DynBuiltin::Mapping(_, _) => Some(VarType::Mapping(node.into())),
            },
            Node::Contract(_) => Some(VarType::User(TypeNode::Contract(node.into()))),
            Node::Function(_) => Some(VarType::User(TypeNode::Func(node.into()))),
            Node::Struct(_) => Some(VarType::User(TypeNode::Struct(node.into()))),
            Node::Enum(_) => Some(VarType::User(TypeNode::Enum(node.into()))),
            Node::Concrete(_) => Some(VarType::Concrete(node.into())),
            Node::ContextVar(cvar) => Some(cvar.ty.clone()),
            Node::Var(var) => VarType::try_from_idx(analyzer, var.ty),
            Node::Ty(ty) => VarType::try_from_idx(analyzer, ty.ty),
            Node::Error(..)
            | Node::ContextFork
            | Node::FunctionCall
            | Node::FunctionParam(..)
            | Node::FunctionReturn(..)
            | Node::ErrorParam(..)
            | Node::Field(..)
            | Node::SourceUnitPart(..)
            | Node::SourceUnit(..)
            | Node::Unresolved(..)
            | Node::Context(..)
            | Node::Msg(_)
            | Node::Block(_) => None,
        }
    }

    pub fn range(&self, analyzer: &impl GraphLike) -> Option<SolcRange> {
        match self {
            Self::BuiltIn(_, Some(range)) => Some(range.clone()),
            Self::BuiltIn(bn, None) => SolcRange::try_from_builtin(bn.underlying(analyzer)),
            Self::Array(_, Some(len_var)) => len_var.latest_version(analyzer).range(analyzer),
            Self::Array(_, None) => SolcRange::try_from_builtin(&Builtin::Uint(256)),
            Self::Concrete(cnode) => SolcRange::from(cnode.underlying(analyzer).clone()),
            _ => None,
        }
    }

    pub fn is_const(&self, analyzer: &impl GraphLike) -> bool {
        match self {
            Self::Concrete(_) => true,
            Self::User(TypeNode::Func(_)) => false,
            _ => {
                if let Some(range) = self.range(analyzer) {
                    range.evaled_range_min(analyzer).range_eq(&range.evaled_range_max(analyzer))
                } else {
                    false
                }
            }
        }
    }

    pub fn func_node(&self, _analyzer: &impl AnalyzerLike) -> Option<FunctionNode> {
        match self {
            Self::User(TypeNode::Func(func_node)) => Some(*func_node),
            _ => None
        }
    }

    pub fn evaled_range(&self, analyzer: &impl AnalyzerLike) -> Option<(Elem<Concrete>, Elem<Concrete>)> {
        self.range(analyzer).map(|range| (
                range.evaled_range_min(analyzer),
                range.evaled_range_max(analyzer),
            ))
    }

    pub fn array_underlying_ty(&self, analyzer: &impl AnalyzerLike) -> VarType {
        match self {
            Self::Array(node, _) => node.underlying_array_ty(analyzer).clone(),
            e => panic!(
                "Node type confusion: expected node to be VarType::Array but it was: {:?}",
                e
            ),
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphLike) -> String {
        match self {
            VarType::User(ty_node) => ty_node.as_string(analyzer),
            VarType::BuiltIn(bn, _) => {
                match analyzer.node(*bn) {
                    Node::Builtin(bi) => bi.as_string(analyzer),
                    _ => unreachable!()
                }
            },
            VarType::Array(dbn, _) => dbn.as_string(analyzer),
            VarType::Mapping(dbn) => dbn.as_string(analyzer),
            VarType::Concrete(c) => {
                c.underlying(analyzer).as_builtin().as_string(analyzer)
            },
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum TypeNode {
    Contract(ContractNode),
    Struct(StructNode),
    Enum(EnumNode),
    Func(FunctionNode),
}

impl TypeNode {
    pub fn as_string(&self, analyzer: &impl GraphLike) -> String {
        match self {
            TypeNode::Contract(n) => format!("contract {}", n.name(analyzer)),
            TypeNode::Struct(n) => format!("struct {}", n.name(analyzer)),
            TypeNode::Enum(n) => format!("enum {}", n.name(analyzer)),
            TypeNode::Func(n) => format!("function {}", n.name(analyzer)),
        }
    }
}

impl From<TypeNode> for NodeIdx {
    fn from(val: TypeNode) -> Self {
        match val {
            TypeNode::Contract(n) => n.into(),
            TypeNode::Struct(n) => n.into(),
            TypeNode::Enum(n) => n.into(),
            TypeNode::Func(n) => n.into(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct BuiltInNode(pub usize);

impl BuiltInNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Builtin {
        match analyzer.node(*self) {
            Node::Builtin(b) => b,
            e => panic!(
                "Node type confusion: expected node to be Builtin but it was: {:?}",
                e
            ),
        }
    }

    pub fn num_size(&self, analyzer: &impl AnalyzerLike) -> Option<u16> {
        let underlying = self.underlying(analyzer);
        underlying.num_size()
    }
}

impl From<NodeIdx> for BuiltInNode {
    fn from(idx: NodeIdx) -> Self {
        BuiltInNode(idx.index())
    }
}

impl From<BuiltInNode> for NodeIdx {
    fn from(val: BuiltInNode) -> Self {
        val.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Builtin {
    Address,
    AddressPayable,
    Payable,
    Bool,
    String,
    Int(u16),
    Uint(u16),
    Bytes(u8),
    Rational,
    DynamicBytes,
    Func(Vec<VarType>, Vec<VarType>),
}

impl Builtin {
    pub fn try_from_ty(ty: Type, analyzer: &mut impl AnalyzerLike<Expr = Expression>) -> Option<Builtin> {
        use Type::*;
        match ty {
            Address => Some(Builtin::Address),
            AddressPayable => Some(Builtin::AddressPayable),
            Payable => Some(Builtin::Payable),
            Bool => Some(Builtin::Bool),
            String => Some(Builtin::String),
            Int(size) => Some(Builtin::Int(size)),
            Uint(size) => Some(Builtin::Uint(size)),
            Bytes(size) => Some(Builtin::Bytes(size)),
            Rational => Some(Builtin::Rational),
            DynamicBytes => Some(Builtin::DynamicBytes),
            Function { params, attributes: _, returns } => {
                let inputs = params.iter().filter_map(|(_, param)| param.as_ref()).map(|param| {
                    analyzer.parse_expr(&param.ty)
                }).collect::<Vec<_>>();
                let inputs = inputs.iter().map(|idx| VarType::try_from_idx(analyzer, *idx).expect("Couldn't parse param")).collect::<Vec<_>>();
                let mut outputs = vec![];
                if let Some((params, _attrs)) = returns {
                    let tmp_outputs = params.iter().filter_map(|(_, param)| param.as_ref()).map(|param| {
                        analyzer.parse_expr(&param.ty)
                    }).collect::<Vec<_>>();
                    outputs = tmp_outputs.iter().map(|idx| VarType::try_from_idx(analyzer, *idx).expect("Couldn't parse output param")).collect::<Vec<_>>();
                }
                Some(Builtin::Func(inputs, outputs))
            }
            _ => None,
        }
    }

    pub fn num_size(&self) -> Option<u16> {
        match self {
            Builtin::Uint(size) => Some(*size),
            Builtin::Int(size) => Some(*size),
            _ => None,
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphLike) -> String {
        use Builtin::*;
        match self {
            Address => "address".to_string(),
            AddressPayable => "payable".to_string(),
            Payable => "payable".to_string(),
            Bool => "bool".to_string(),
            String => "string".to_string(),
            Int(size) => format!("int{}", size),
            Uint(size) => format!("uint{}", size),
            Bytes(size) => format!("bytes{}", size),
            Rational => "rational".to_string(),
            DynamicBytes => "bytes".to_string(),
            Func(inputs, outputs) => format!("function({}) returns ({})",
                inputs.iter().map(|input| input.as_string(analyzer)).collect::<Vec<_>>().join(", "), outputs.iter().map(|output| output.as_string(analyzer)).collect::<Vec<_>>().join(", "))
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct DynBuiltInNode(pub usize);

impl DynBuiltInNode {
    pub fn underlying_array_ty<'a>(&self, analyzer: &'a impl GraphLike) -> &'a VarType {
        match analyzer.node(*self) {
            Node::DynBuiltin(DynBuiltin::Array(v)) => v,
            e => panic!(
                "Node type confusion: expected node to be Array but it was: {:?}",
                e
            ),
        }
    }

    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a DynBuiltin {
        match analyzer.node(*self) {
            Node::DynBuiltin(b) => b,
            e => panic!(
                "Node type confusion: expected node to be DynBuiltin but it was: {:?}",
                e
            ),
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).as_string(analyzer)
    }
}

impl From<DynBuiltInNode> for NodeIdx {
    fn from(val: DynBuiltInNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for DynBuiltInNode {
    fn from(idx: NodeIdx) -> Self {
        DynBuiltInNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum DynBuiltin {
    Array(VarType),
    Mapping(VarType, VarType),
}

impl DynBuiltin {
    pub fn as_string(&self, analyzer: &impl GraphLike) -> String {
        use DynBuiltin::*;
        match self {
            Array(v_ty) => format!("{}[]", v_ty.as_string(analyzer)),
            Mapping(key_ty, v_ty) => format!("mapping({} => {})", key_ty.as_string(analyzer), v_ty.as_string(analyzer)),
        }
    }
}
