use crate::{
    nodes::{Concrete, ContractNode},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, Edge, GraphBackend, Node, VarType,
};

use shared::{FlatExpr, GraphError, NodeIdx, RangeArena};

use petgraph::visit::EdgeRef;
use solang_parser::pt::{Expression, Identifier, Loc, TypeDefinition};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct YulFunctionNode(pub usize);
impl YulFunctionNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a YulFunction, GraphError> {
        match analyzer.node(*self) {
            Node::YulFunction(ty) => Ok(ty),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be YulFunctionNode but it was: {e:?}"
            ))),
        }
    }

    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self.underlying(analyzer)?.name.to_string())
    }
    pub fn exprs(&self, analyzer: &impl GraphBackend) -> Result<Vec<FlatExpr>, GraphError> {
        Ok(self.underlying(analyzer)?.exprs.clone())
    }
}

impl From<YulFunctionNode> for NodeIdx {
    fn from(val: YulFunctionNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for YulFunctionNode {
    fn from(idx: NodeIdx) -> Self {
        YulFunctionNode(idx.index())
    }
}

impl AsDotStr for YulFunctionNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!("yul function {}", underlying.name,)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct YulFunction {
    pub loc: Loc,
    pub name: &'static str,
    pub exprs: Vec<FlatExpr>,
}

impl From<YulFunction> for Node {
    fn from(val: YulFunction) -> Self {
        Node::YulFunction(val)
    }
}

impl YulFunction {
    pub fn new(exprs: Vec<FlatExpr>, name: &'static str, loc: Loc) -> YulFunction {
        YulFunction { loc, name, exprs }
    }
}
