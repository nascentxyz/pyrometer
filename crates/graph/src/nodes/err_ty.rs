use crate::{AnalyzerBackend, AsDotStr, GraphBackend, GraphError, Node};

use shared::NodeIdx;
use solang_parser::pt::{ErrorDefinition, ErrorParameter, Expression, Identifier, Loc};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ErrorNode(pub usize);
impl ErrorNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Error, GraphError> {
        match analyzer.node(*self) {
            Node::Error(err) => Ok(err),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Var but it was: {e:?}"
            ))),
        }
    }
}
impl AsDotStr for ErrorNode {
    fn as_dot_str(&self, analyzer: &impl GraphBackend) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "error {}",
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
        )
    }
}

impl From<ErrorNode> for NodeIdx {
    fn from(val: ErrorNode) -> Self {
        val.0.into()
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

impl From<Error> for Node {
    fn from(val: Error) -> Self {
        Node::Error(val)
    }
}

impl From<ErrorDefinition> for Error {
    fn from(con: ErrorDefinition) -> Error {
        Error {
            loc: con.loc,
            name: con.name,
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

impl From<ErrorParamNode> for NodeIdx {
    fn from(val: ErrorParamNode) -> Self {
        val.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ErrorParam {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub name: Option<Identifier>,
}

impl From<ErrorParam> for Node {
    fn from(val: ErrorParam) -> Self {
        Node::ErrorParam(val)
    }
}

impl ErrorParam {
    pub fn new(
        analyzer: &mut (impl GraphBackend + AnalyzerBackend<Expr = Expression>),
        param: ErrorParameter,
    ) -> Self {
        ErrorParam {
            loc: param.loc,
            ty: analyzer.parse_expr(&param.ty, None),
            name: param.name,
        }
    }
}
