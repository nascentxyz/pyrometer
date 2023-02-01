use crate::{analyzer::AnalyzerLike, Node, NodeIdx};
use solang_parser::pt::{Identifier, Loc, VariableAttribute, VariableDefinition, Expression};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarNode(pub usize);

impl VarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Var {
        match analyzer.node(*self) {
            Node::Var(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Var but it was: {:?}",
                e
            ),
        }
    }

    pub fn name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed function")
            .name
    }
}

impl Into<NodeIdx> for VarNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for VarNode {
    fn from(idx: NodeIdx) -> Self {
        VarNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Var {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub attrs: Vec<VariableAttribute>,
    pub name: Option<Identifier>,
    pub initializer: Option<NodeIdx>,
    pub in_contract: bool,
}

impl Into<Node> for Var {
    fn into(self) -> Node {
        Node::Var(self)
    }
}

impl Var {
    pub fn new(
        analyzer: &mut impl AnalyzerLike<Expr = Expression>,
        var: VariableDefinition,
        in_contract: bool,
    ) -> Var {
        Var {
            loc: var.loc,
            ty: analyzer.parse_expr(&var.ty),
            attrs: var.attrs,
            name: var.name,
            initializer: if let Some(init) = var.initializer {
                Some(analyzer.parse_expr(&init))
            } else {
                None
            },
            in_contract,
        }
    }
}
