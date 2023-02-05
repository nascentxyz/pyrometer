use crate::nodes::ContractNode;
use crate::range::SolcRange;
use crate::VarType;
use solang_parser::pt::Statement;
use crate::Edge;
use crate::context::{ContextEdge, ContextNode};
use petgraph::{Direction, visit::EdgeRef};
use crate::{analyzer::AnalyzerLike, Node, NodeIdx};
use solang_parser::pt::{
    FunctionAttribute, FunctionDefinition, FunctionTy, Identifier, Loc, Parameter, StorageLocation, Expression
};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionNode(pub usize);
impl FunctionNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Function {
        match analyzer.node(*self) {
            Node::Function(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Function but it was: {:?}",
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

    pub fn body_ctx<'a>(&self, analyzer: &'a impl AnalyzerLike) -> ContextNode {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Context) == *edge.weight())
            .map(|edge| ContextNode::from(edge.source()))
            .take(1)
            .next()
            .expect("No context for function")
    }

    pub fn params<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Vec<FunctionParamNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionParam == *edge.weight())
            .map(|edge| FunctionParamNode::from(edge.source()))
            .collect()
    }

    pub fn contract<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<ContractNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Func == *edge.weight())
            .map(|edge| ContractNode::from(edge.target()))
            .take(1)
            .next()
    }
}

impl Into<NodeIdx> for FunctionNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for FunctionNode {
    fn from(idx: NodeIdx) -> Self {
        FunctionNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Function {
    pub loc: Loc,
    pub ty: FunctionTy,
    pub name: Option<Identifier>,
    pub name_loc: Loc,
    pub attributes: Vec<FunctionAttribute>,
    pub body: Option<Statement>
}

impl Into<Node> for Function {
    fn into(self) -> Node {
        Node::Function(self)
    }
}

impl From<FunctionDefinition> for Function {
    fn from(func: FunctionDefinition) -> Function {
        Function {
            loc: func.loc,
            ty: func.ty,
            name: func.name,
            name_loc: func.name_loc,
            attributes: func.attributes,
            body: func.body,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionParamNode(pub usize);

impl FunctionParamNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a FunctionParam {
        match analyzer.node(*self) {
            Node::FunctionParam(param) => param,
            e => panic!(
                "Node type confusion: expected node to be FunctionParam but it was: {:?}",
                e
            ),
        }
    }

    pub fn name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed function parameter")
            .name
    }

    pub fn maybe_name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<String> {
        Some(self.underlying(analyzer)
            .name
            .clone()?
            .name)
    }

    pub fn range<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<SolcRange> {
        let ty_node = self.underlying(analyzer).ty;
        let var_ty = VarType::try_from_idx(analyzer, ty_node)?;
        var_ty.range(analyzer)
    }

    pub fn loc<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Loc {
        self.underlying(analyzer).loc
    }
}

impl Into<NodeIdx> for FunctionParamNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for FunctionParamNode {
    fn from(idx: NodeIdx) -> Self {
        FunctionParamNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionParam {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub storage: Option<StorageLocation>,
    pub name: Option<Identifier>,
}

impl Into<Node> for FunctionParam {
    fn into(self) -> Node {
        Node::FunctionParam(self)
    }
}

impl FunctionParam {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, param: Parameter) -> Self {
        FunctionParam {
            loc: param.loc,
            ty: analyzer.parse_expr(&param.ty),
            storage: param.storage,
            name: param.name,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionReturnNode(pub usize);

impl FunctionReturnNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a FunctionReturn {
        match analyzer.node(*self) {
            Node::FunctionReturn(ret) => ret,
            e => panic!(
                "Node type confusion: expected node to be FunctionParam but it was: {:?}",
                e
            ),
        }
    }
}

impl Into<NodeIdx> for FunctionReturnNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for FunctionReturnNode {
    fn from(idx: NodeIdx) -> Self {
        FunctionReturnNode(idx.index())
    }
}

impl Into<Node> for FunctionReturn {
    fn into(self) -> Node {
        Node::FunctionReturn(self)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct FunctionReturn {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub storage: Option<StorageLocation>,
    pub name: Option<Identifier>,
}

impl FunctionReturn {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, param: Parameter) -> Self {
        FunctionReturn {
            loc: param.loc,
            ty: analyzer.parse_expr(&param.ty),
            storage: param.storage,
            name: param.name,
        }
    }
}
