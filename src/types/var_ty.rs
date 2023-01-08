use crate::AnalyzerLike;
use crate::Analyzer;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{Loc, VariableAttribute, Identifier, VariableDefinition};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarNode(pub usize);

impl Into<NodeIdx> for VarNode {
	fn into(self) -> NodeIdx {
		self.0.into()
	}
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Var {
	pub loc: Loc,
	pub ty: NodeIdx,
	pub attrs: Vec<VariableAttribute>,
	pub name: Option<Identifier>,
	pub initializer: Option<NodeIdx>,
}

impl Into<Node> for Var {
	fn into(self) -> Node {
		Node::Var(self)
	}
}

impl Var {
	pub fn new(analyzer: &mut impl AnalyzerLike, var: VariableDefinition) -> Var {
		Var {
			loc: var.loc,
			ty: analyzer.parse_expr(&var.ty),
			attrs: var.attrs,
			name: var.name,
			initializer: if let Some(init) = var.initializer { Some(analyzer.parse_expr(&init)) } else { None },
		}
	}
}