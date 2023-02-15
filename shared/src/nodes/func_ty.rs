use crate::analyzer::AsDotStr;
use crate::nodes::ContractNode;
use crate::range::SolcRange;
use crate::VarType;
use solang_parser::pt::Statement;
use crate::Edge;
use crate::context::{ContextEdge, ContextNode};
use petgraph::{Direction, visit::EdgeRef};
use crate::{analyzer::{GraphLike, AnalyzerLike}, Node, NodeIdx};
use solang_parser::pt::{
    Visibility, FunctionAttribute, FunctionDefinition, FunctionTy, Identifier, Loc, Parameter, StorageLocation, Expression
};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionNode(pub usize);
impl FunctionNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Function {
        match analyzer.node(*self) {
            Node::Function(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Function but it was: {:?}",
                e
            ),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        match self.underlying(analyzer).ty {
            FunctionTy::Constructor
            | FunctionTy::Receive
            | FunctionTy::Fallback => "".to_string(),
            _ => self.underlying(analyzer)
                .name
                .clone()
                .expect("Unnamed function")
                .name
        }
    }

    pub fn body_ctx(&self, analyzer: &'_ impl GraphLike) -> ContextNode {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Context) == *edge.weight())
            .map(|edge| ContextNode::from(edge.source()))
            .take(1)
            .next()
            .expect("No context for function")
    }

    pub fn params(&self, analyzer: &'_ impl GraphLike) -> Vec<FunctionParamNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionParam == *edge.weight())
            .map(|edge| FunctionParamNode::from(edge.source()))
            .collect()
    }

    pub fn contract(&self, analyzer: &'_ impl GraphLike) -> Option<ContractNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Func == *edge.weight())
            .map(|edge| edge.target())
            .filter(|node| matches!(analyzer.node(*node), Node::Contract(_)))
            .map(ContractNode::from)
            .take(1)
            .next()
    }

    pub fn is_public_or_ext(&self, analyzer: &'_ impl GraphLike) -> bool {
        self.underlying(analyzer).attributes.iter().any(|attr| {
            matches!(attr,
                FunctionAttribute::Visibility(Visibility::Public(_))
                | FunctionAttribute::Visibility(Visibility::External(_))
            )
        })
    }
}

impl AsDotStr for FunctionNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let inputs = self.params(analyzer).iter().map(|param_node: &FunctionParamNode| {
            param_node.as_dot_str(analyzer)
        }).collect::<Vec<_>>().join(", ");

        let attrs = self.underlying(analyzer).attributes.iter().map(|attr| {
            match attr {
                FunctionAttribute::Mutability(inner) => format!("{}", inner),
                FunctionAttribute::Visibility(inner) => format!("{}", inner),
                FunctionAttribute::Virtual(_) => "virtual".to_string(),
                FunctionAttribute::Immutable(_) => "immutable".to_string(),
                FunctionAttribute::Override(_, _) => "override".to_string(),
                _ => "".to_string()
            }
        }).collect::<Vec<_>>().join(" ");
        format!("{} {}({}) {}", self.underlying(analyzer).ty, self.name(analyzer), inputs, attrs)
    }
}

impl From<FunctionNode> for NodeIdx {
    fn from(val: FunctionNode) -> Self {
        val.0.into()
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

impl From<Function> for Node {
    fn from(val: Function) -> Self {
        Node::Function(val)
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

impl AsDotStr for FunctionParamNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty).expect("Non-typeable as type");
        format!("{}{}{}",
            var_ty.as_dot_str(analyzer),
            if let Some(stor) = &self.underlying(analyzer).storage {
                format!(" {} ", stor)
            } else {
                "".to_string()
            },
            if let Some(name) = self.maybe_name(analyzer) {
                name
            } else {
                "".to_string()
            }
        )
    }
}

impl FunctionParamNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a FunctionParam {
        match analyzer.node(*self) {
            Node::FunctionParam(param) => param,
            e => panic!(
                "Node type confusion: expected node to be FunctionParam but it was: {:?}",
                e
            ),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed function parameter")
            .name
    }

    pub fn maybe_name(&self, analyzer: &'_ impl GraphLike) -> Option<String> {
        Some(self.underlying(analyzer)
            .name
            .clone()?
            .name)
    }

    pub fn range(&self, analyzer: &'_ impl GraphLike) -> Option<SolcRange> {
        let ty_node = self.underlying(analyzer).ty;
        let var_ty = VarType::try_from_idx(analyzer, ty_node)?;
        var_ty.range(analyzer)
    }

    pub fn loc(&self, analyzer: &'_ impl GraphLike) -> Loc {
        self.underlying(analyzer).loc
    }
}

impl From<FunctionParamNode> for NodeIdx {
    fn from(val: FunctionParamNode) -> Self {
        val.0.into()
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

impl From<FunctionParam> for Node {
    fn from(val: FunctionParam) -> Self {
        Node::FunctionParam(val)
    }
}

impl FunctionParam {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, param: Parameter) -> Self {
        println!("func param: {:?}", param.name);
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

impl AsDotStr for FunctionReturnNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty).expect("Non-typeable as type");
        format!("{}{}{}",
            var_ty.as_dot_str(analyzer),
            if let Some(stor) = &self.underlying(analyzer).storage {
                format!(" {} ", stor)
            } else {
                "".to_string()
            },
            if let Some(name) = self.maybe_name(analyzer) {
                name
            } else {
                "".to_string()
            }
        )
    }
}

impl FunctionReturnNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a FunctionReturn {
        match analyzer.node(*self) {
            Node::FunctionReturn(ret) => ret,
            e => panic!(
                "Node type confusion: expected node to be FunctionParam but it was: {:?}",
                e
            ),
        }
    }

    pub fn maybe_name(&self, analyzer: &'_ impl GraphLike) -> Option<String> {
        Some(self.underlying(analyzer)
            .name
            .clone()?
            .name)
    }
}

impl From<FunctionReturnNode> for NodeIdx {
    fn from(val: FunctionReturnNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for FunctionReturnNode {
    fn from(idx: NodeIdx) -> Self {
        FunctionReturnNode(idx.index())
    }
}

impl From<FunctionReturn> for Node {
    fn from(val: FunctionReturn) -> Self {
        Node::FunctionReturn(val)
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
