use crate::AnalyzerLike;
use crate::Analyzer;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{Loc, Identifier, ErrorDefinition, ErrorParameter};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ErrorNode(pub usize);

impl Into<NodeIdx> for ErrorNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for ErrorNode {
	fn from(idx: NodeIdx) -> Self {
		ErrorNode(idx.index())
	}
}


#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Error {
	pub loc: Loc,
	pub name: Option<Identifier>,
}

impl Into<Node> for Error {
	fn into(self) -> Node {
		Node::Error(self)
	}
}

impl From<ErrorDefinition> for Error {
	fn from(con: ErrorDefinition) -> Error {
		Error {
			loc: con.loc,
			name: con.name
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ErrorParamNode(pub usize);

impl From<NodeIdx> for ErrorParamNode {
	fn from(idx: NodeIdx) -> Self {
		ErrorParamNode(idx.index())
	}
}

impl Into<NodeIdx> for ErrorParamNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}


#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ErrorParam {
	pub loc: Loc,
	pub ty: NodeIdx,
	pub name: Option<Identifier>,
}

impl Into<Node> for ErrorParam {
	fn into(self) -> Node {
		Node::ErrorParam(self)
	}
}

impl ErrorParam {
	pub fn new(analyzer: &mut impl AnalyzerLike, param: ErrorParameter) -> Self {
		ErrorParam {
			loc: param.loc,
			ty: analyzer.parse_expr(&param.ty),
			name: param.name,
		}
	}
}
