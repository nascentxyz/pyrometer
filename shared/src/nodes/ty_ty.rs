use crate::analyzer::AnalyzerLike;
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{Identifier, Loc, TypeDefinition, Expression};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TyNode(pub usize);

impl Into<NodeIdx> for TyNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ty {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub name: Identifier,
}

impl Into<Node> for Ty {
    fn into(self) -> Node {
        Node::Ty(self)
    }
}

impl Ty {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, ty: TypeDefinition) -> Ty {
        Ty {
            loc: ty.loc,
            ty: analyzer.parse_expr(&ty.ty),
            name: ty.name,
        }
    }
}
