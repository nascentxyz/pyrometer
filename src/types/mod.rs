use crate::AnalyzerLike;
use crate::ConcreteNode;
use crate::GraphLike;
use crate::Analyzer;
use crate::NodeIdx;
use crate::Node;
use solang_parser::pt::Type;
use ethers_core::types::U256;

pub mod contract_ty;
pub use contract_ty::*;
pub mod enum_ty;
pub use enum_ty::*;
pub mod struct_ty;
pub use struct_ty::*;
pub mod func_ty;
pub use func_ty::*;
pub mod err_ty;
pub use err_ty::*;
pub mod var_ty;
pub use var_ty::*;
pub mod ty_ty;
pub use ty_ty::*;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Range {
	pub min: RangeElem,
	pub max: RangeElem,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum RangeElem {
	Concrete(U256),
	Dynamic(NodeIdx)
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct LenRange {
	pub min: RangeElem,
	pub max: RangeElem,
}

impl Range {
	pub fn try_from_builtin(builtin: &Builtin) -> Option<Self> {
		match builtin {
			Builtin::Uint(size) => {
				if *size == 256 {
					Some(Range { min: RangeElem::Concrete(0.into()), max: RangeElem::Concrete(U256::MAX) })
				} else {
					Some(Range { min: RangeElem::Concrete(0.into()), max: RangeElem::Concrete(U256::from(2).pow(U256::from(*size)) - 1) })
				}
			},
			_ => None
		}
	}
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum VarType {
	User(TypeNode),
	BuiltIn(BuiltInNode, Option<Range>),
	Array(DynBuiltInNode, Option<LenRange>),
	Mapping(DynBuiltInNode),
	Concrete(ConcreteNode),
}

impl VarType {
	pub fn try_from_idx(analyzer: &(impl AnalyzerLike + ?Sized), node: NodeIdx) -> Option<VarType> {
		// get node, check if typeable and convert idx into vartype
		match analyzer.node(node) {
			Node::VarType(a) => Some(a.clone()),
		    Node::Builtin(b) => Some(VarType::BuiltIn(node.into(), Range::try_from_builtin(b))),
		    Node::DynBuiltin(dyn_b) => {
		    	match dyn_b {
		    		DynBuiltin::Array(_) => Some(VarType::Array(node.into(), Some(LenRange { min: RangeElem::Concrete(U256::zero()), max: RangeElem::Concrete(U256::MAX)}))),
		    		DynBuiltin::Mapping(_, _) => Some(VarType::Mapping(node.into())),
		    	}
		    },
		    Node::Contract(_) => Some(VarType::User(TypeNode::Contract(node.into()))),
		    Node::Function(_) => Some(VarType::User(TypeNode::Func(node.into()))),
		    Node::Struct(_)   => Some(VarType::User(TypeNode::Struct(node.into()))),
		    Node::Enum(_)     => Some(VarType::User(TypeNode::Enum(node.into()))),
		    Node::Concrete(_) => Some(VarType::Concrete(node.into())),
		    Node::ContextVar(cvar) => Some(cvar.ty.clone()),
		    Node::Var(var)    => VarType::try_from_idx(analyzer, var.ty),
		    Node::Ty(ty)      => VarType::try_from_idx(analyzer, ty.ty),
		    Node::Error(..)
		    | Node::FunctionParam(..)
		    | Node::FunctionReturn(..)
		    | Node::ErrorParam(..)
		    | Node::Field(..)
		    | Node::SourceUnitPart(..)
		    | Node::SourceUnit(..)
		    | Node::Unresolved(..)
		    | Node::Context(..) => None
		}
	}

	pub fn range(&self) -> Option<Range> {
		match self {
			Self::BuiltIn(_, range) => {
				range.clone()
			}
			_ => None
		}
	}

	pub fn array_underlying_ty(&self, analyzer: &impl AnalyzerLike) -> VarType {
		match self {
			Self::Array(node, _) => {
				node.underlying_array_ty(analyzer).clone()
			}
			e => panic!("Node type confusion: expected node to be VarType::Array but it was: {:?}", e)
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

impl Into<NodeIdx> for TypeNode {
	fn into(self) -> NodeIdx {
		match self {
			Self::Contract(n) => n.into(),
			Self::Struct(n) => n.into(),
			Self::Enum(n) => n.into(),
			Self::Func(n) => n.into(),
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct BuiltInNode(pub usize);

impl BuiltInNode {
	pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Builtin {
		match analyzer.node(*self) {
			Node::Builtin(b) => b,
			e => panic!("Node type confusion: expected node to be Builtin but it was: {:?}", e)
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

impl Into<NodeIdx> for BuiltInNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
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
}

impl Builtin {
	pub fn try_from_ty(ty: Type) -> Option<Builtin> {
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
		    _ => None
		}
	}

	pub fn num_size(&self) -> Option<u16> {
		match self {
			Builtin::Uint(size) => Some(*size),
			Builtin::Int(size) => Some(*size),
			_ => None
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct DynBuiltInNode(pub usize);

impl DynBuiltInNode {
	pub fn underlying_array_ty<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a VarType {
		match analyzer.node(*self) {
			Node::DynBuiltin(DynBuiltin::Array(v)) => v,
			e => panic!("Node type confusion: expected node to be Array but it was: {:?}", e)
		}
	}
}

impl Into<NodeIdx> for DynBuiltInNode {
	fn into(self) -> NodeIdx {
		self.0.into()
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
