use crate::AnalyzerLike;
use crate::{Analyzer, Node, NodeIdx};
use solang_parser::pt::{Loc, Identifier, FunctionTy, FunctionDefinition, Parameter, StorageLocation, FunctionAttribute,};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionNode(pub usize);
impl FunctionNode {
	pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Function {
		match analyzer.node(*self) {
			Node::Function(func) => func,
			e => panic!("Node type confusion: expected node to be Function but it was: {:?}", e)
		}
	}
}

impl Into<NodeIdx> for FunctionNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for FunctionNode {
	fn from(idx: NodeIdx) -> Self {
		FunctionNode(idx.index())
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Function {
	pub loc: Loc,
	pub ty: FunctionTy,
	pub name: Option<Identifier>,
	pub name_loc: Loc,
	pub attributes: Vec<FunctionAttribute>,
}

impl Into<Node> for Function {
	fn into(self) -> Node {
		Node::Function(self)
	}
}

impl From<FunctionDefinition> for Function {
	fn from(func: FunctionDefinition) -> Function {
		Function {
			loc: func.loc,
			ty: func.ty,
			name: func.name,
			name_loc: func.name_loc,
			attributes: func.attributes
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionParamNode(pub usize);

impl FunctionParamNode {
	pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a FunctionParam {
		match analyzer.node(*self) {
			Node::FunctionParam(param) => param,
			e => panic!("Node type confusion: expected node to be FunctionParam but it was: {:?}", e)
		}
	}
}


impl Into<NodeIdx> for FunctionParamNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for FunctionParamNode {
	fn from(idx: NodeIdx) -> Self {
		FunctionParamNode(idx.index())
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionParam {
	pub loc: Loc,
	pub ty: NodeIdx,
	pub storage: Option<StorageLocation>,
	pub name: Option<Identifier>,
}

impl Into<Node> for FunctionParam {
	fn into(self) -> Node {
		Node::FunctionParam(self)
	}
}

impl FunctionParam {
	pub fn new(analyzer: &mut impl AnalyzerLike, param: Parameter) -> Self {
		FunctionParam {
			loc: param.loc,
			ty: analyzer.parse_expr(&param.ty),
			storage: param.storage,
			name: param.name,
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionReturnNode(pub usize);

impl FunctionReturnNode {
	pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a FunctionReturn {
		match analyzer.node(*self) {
			Node::FunctionReturn(ret) => ret,
			e => panic!("Node type confusion: expected node to be FunctionParam but it was: {:?}", e)
		}
	}
}

impl Into<NodeIdx> for FunctionReturnNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for FunctionReturnNode {
	fn from(idx: NodeIdx) -> Self {
		FunctionReturnNode(idx.index())
	}
}

impl Into<Node> for FunctionReturn {
	fn into(self) -> Node {
		Node::FunctionReturn(self)
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionReturn {
	pub loc: Loc,
	pub ty: NodeIdx,
	pub storage: Option<StorageLocation>,
	pub name: Option<Identifier>,
}

impl FunctionReturn {
	pub fn new(analyzer: &mut impl AnalyzerLike, param: Parameter) -> Self {
		FunctionReturn {
			loc: param.loc,
			ty: analyzer.parse_expr(&param.ty),
			storage: param.storage,
			name: param.name,
		}
	}
}
