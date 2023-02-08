use crate::analyzer::AsDotStr;
use crate::VarType;
use crate::analyzer::{GraphLike, AnalyzerLike};
use crate::Node;
use crate::NodeIdx;
use solang_parser::pt::{Identifier, Loc, TypeDefinition, Expression};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TyNode(pub usize);
impl TyNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Ty {
        match analyzer.node(*self) {
            Node::Ty(ty) => ty,
            e => panic!(
                "Node type confusion: expected node to be Ty but it was: {:?}",
                e
            ),
        }
    }
}
impl From<TyNode> for NodeIdx {
    fn from(val: TyNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for TyNode {
    fn from(idx: NodeIdx) -> Self {
        TyNode(idx.index())
    }
}

impl AsDotStr for TyNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer)
            } else {
                "".to_string()
            },
            underlying.name.name,
        )
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Ty {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub name: Identifier,
}

impl From<Ty> for Node {
    fn from(val: Ty) -> Self {
        Node::Ty(val)
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
