use crate::AnalyzerLike;
use crate::AsDotStr;
use crate::{analyzer::GraphLike, Node, NodeIdx};
use solang_parser::pt::{ErrorDefinition, ErrorParameter, Identifier, Loc, Expression};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ErrorNode(pub usize);
impl ErrorNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Error {
        match analyzer.node(*self) {
            Node::Error(err) => err,
            e => panic!(
                "Node type confusion: expected node to be Var but it was: {:?}",
                e
            ),
        }
    }
}
impl AsDotStr for ErrorNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("error {}",
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
        )
    }
}

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
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, param: ErrorParameter) -> Self {
        ErrorParam {
            loc: param.loc,
            ty: analyzer.parse_expr(&param.ty),
            name: param.name,
        }
    }
}
