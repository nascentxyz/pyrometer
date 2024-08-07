use crate::{
    nodes::{Concrete, ContractNode},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, Edge, GraphBackend, Node, VarType,
};

use shared::{GraphError, NodeIdx, RangeArena};

use petgraph::visit::EdgeRef;
use solang_parser::pt::{Expression, Identifier, Loc, TypeDefinition};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct TyNode(pub usize);
impl TyNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Ty, GraphError> {
        match analyzer.node(*self) {
            Node::Ty(ty) => Ok(ty),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be TypeNode but it was: {e:?}"
            ))),
        }
    }

    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.name.to_string())
    }

    pub fn maybe_associated_contract(&self, analyzer: &impl GraphBackend) -> Option<ContractNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), petgraph::Direction::Outgoing)
            .filter(|edge| matches!(*edge.weight(), Edge::Ty))
            .filter_map(|edge| {
                let node = edge.target();
                match analyzer.node(node) {
                    Node::Contract(_) => Some(ContractNode::from(node)),
                    _ => None,
                }
            })
            .take(1)
            .next()
            .map(ContractNode::from)
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
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer, arena)
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
    pub fn new(
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
        ty: TypeDefinition,
    ) -> Ty {
        Ty {
            loc: ty.loc,
            ty: analyzer.parse_expr(arena, &ty.ty, None),
            name: ty.name,
        }
    }
}
