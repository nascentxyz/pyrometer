use crate::AnalyzerLike;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{Loc, Identifier, StructDefinition, VariableDeclaration};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct StructNode(pub usize);

impl StructNode {
	pub fn loc(&self, analyzer: &impl AnalyzerLike) -> Loc {
		Struct::maybe_from_node(analyzer.node(*self).clone()).expect("Node wasnt struct").loc
	}

	pub fn name(&self, analyzer: &impl AnalyzerLike) -> String {
		Struct::maybe_from_node(analyzer.node(*self).clone()).expect("Node wasnt struct").name.expect("Struct wasn't named").to_string()
	}
}

impl Into<NodeIdx> for StructNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

impl From<NodeIdx> for StructNode {
	fn from(idx: NodeIdx) -> Self {
		StructNode(idx.index())
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Struct {
	pub loc: Loc,
	pub name: Option<Identifier>,
}

impl Struct {
	pub fn maybe_from_node(node: Node) -> Option<Self> {
		match node {
			Node::Struct(s) => Some(s),
			_ => None,
		}
	}
}

impl Into<Node> for Struct {
	fn into(self) -> Node {
		Node::Struct(self)
	}
}

impl From<StructDefinition> for Struct {
	fn from(con: StructDefinition) -> Struct {
		Struct {
			loc: con.loc,
			name: con.name
		}
	}
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FieldNode(pub usize);

impl FieldNode {
	pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Field {
		match analyzer.node(*self) {
			Node::Field(field) => field,
			e => panic!("Node type confusion: expected node to be Field but it was: {:?}", e)
		}
	}
}

impl From<NodeIdx> for FieldNode {
	fn from(idx: NodeIdx) -> Self {
		FieldNode(idx.index())
	}
}

impl Into<NodeIdx> for FieldNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Field {
	pub loc: Loc,
	pub ty: NodeIdx,
	pub name: Option<Identifier>,
}

impl Into<Node> for Field {
	fn into(self) -> Node {
		Node::Field(self)
	}
}

impl Field {
	pub fn new(analyzer: &mut impl AnalyzerLike, var_def: VariableDeclaration) -> Field {
		let ty_idx = analyzer.parse_expr(&var_def.ty);
		Field {
			loc: var_def.loc,
			ty: ty_idx,
			name: var_def.name
		}
	}
}