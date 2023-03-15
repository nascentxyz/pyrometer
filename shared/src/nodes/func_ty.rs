use solang_parser::pt::VariableDefinition;
use std::collections::BTreeMap;
use solang_parser::pt::ParameterList;
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
    Visibility, FunctionAttribute, FunctionDefinition, FunctionTy, Identifier, Loc, Parameter, StorageLocation, Expression, Base,
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

    pub fn modifiers(&self, analyzer: &impl GraphLike) -> Vec<FunctionNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter_map(|edge| {
                if let Edge::FuncModifier(order) = *edge.weight() {
                    Some((order, FunctionNode::from(edge.source())))
                } else {
                    None
                }
            })
            .collect::<BTreeMap<_,_>>().values().copied()
            .collect()
    }

    pub fn modifier_input_vars(&self, mod_num: usize, analyzer: &impl GraphLike) -> Vec<Expression> {
        let modifiers = self.underlying(analyzer).modifiers_as_base();
        if let Some(modifier) = modifiers.get(mod_num) {
            if let Some(args) = &modifier.args {
                args.to_vec()
            } else {
                vec![]    
            }
        } else {
            vec![]
        }
    }

    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl GraphLike) -> &'a mut Function {
        match analyzer.node_mut(*self) {
            Node::Function(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Function but it was: {:?}",
                e
            ),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        match self.underlying(analyzer).ty {
            FunctionTy::Constructor => format!("constructor({})", self.params(analyzer).iter().map(|param| {param.ty_str(analyzer)}).collect::<Vec<_>>().join(", ")),
            FunctionTy::Receive  => "receive()".to_string(),
            FunctionTy::Fallback => "fallback()".to_string(),
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

    pub fn maybe_body_ctx(&self, analyzer: &'_ impl GraphLike) -> Option<ContextNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Context) == *edge.weight())
            .map(|edge| ContextNode::from(edge.source()))
            .take(1)
            .next()
    }

    pub fn params(&self, analyzer: &'_ impl GraphLike) -> Vec<FunctionParamNode> {
        let mut params = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionParam == *edge.weight())
            .map(|edge| FunctionParamNode::from(edge.source()))
            .collect::<Vec<_>>();
        params.sort_by(|a, b| a.underlying(analyzer).order.cmp(&b.underlying(analyzer).order));
        params
    }

    pub fn set_params_and_ret(&self, analyzer: &'_ mut (impl GraphLike + AnalyzerLike<Expr = Expression>)) {
         let underlying = self.underlying(analyzer).clone();
         let mut params_strs = vec![];
         underlying.params.into_iter().enumerate().for_each(|(i, (_loc, input))| {
            if let Some(input) = input {
                let param = FunctionParam::new(analyzer, input, i);
                let input_node = analyzer.add_node(param);
                params_strs.push(FunctionParamNode::from(input_node).ty_str(analyzer));
                analyzer.add_edge(input_node, *self, Edge::FunctionParam);
            }
        });
        underlying.returns.into_iter().for_each(|(_loc, output)| {
            if let Some(output) = output {
                let ret = FunctionReturn::new(analyzer, output);
                let output_node = analyzer.add_node(ret);
                analyzer.add_edge(output_node, *self, Edge::FunctionReturn);
            }
        });

        let underlying_mut = self.underlying_mut(analyzer);
        if let Some(ref mut name) = underlying_mut.name {
            name.name = format!("{}({})", name.name, params_strs.join(", "));
        }
    }

    pub fn set_modifiers(&self, analyzer: &mut (impl GraphLike + AnalyzerLike<Expr = Expression>)) {
        let modifiers = self.underlying(analyzer).clone().modifiers(self.params(analyzer), analyzer);
        modifiers.iter().enumerate().for_each(|(i, modifier)| {
            analyzer.add_edge(*modifier, *self, Edge::FuncModifier(i))
        });
    }

    pub fn returns(&self, analyzer: &'_ impl GraphLike) -> Vec<FunctionReturnNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionReturn == *edge.weight())
            .map(|edge| FunctionReturnNode::from(edge.source()))
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
    pub body: Option<Statement>,
    pub params: ParameterList,
    pub returns: ParameterList,
}

impl Function {
    pub fn modifiers(&self, func_params: Vec<FunctionParamNode>, analyzer: &(impl GraphLike + AnalyzerLike<Expr = Expression>)) -> Vec<FunctionNode> {
        use std::fmt::Write;
        let modifiers = self.modifiers_as_base();
        if modifiers.is_empty() {
            vec![]
        } else {
            modifiers.iter().filter_map(|modifier| {
                assert_eq!(modifier.name.identifiers.len(), 1);
                // construct arg string for function selector
                let mut mod_name = format!("{}(", modifier.name.identifiers[0]);
                if let Some(args) = &modifier.args {
                    let args_str = args.iter().map(|expr| {
                        match expr {
                            Expression::Variable(ident) => {
                                let func_param_ty_str = func_params.iter().find(|param| {
                                    if let Some(param_name) = param.maybe_name(analyzer) {
                                        param_name == ident.name
                                    } else {
                                        false
                                    }
                                }).map(|param| param.ty_str(analyzer)).unwrap_or_else(|| "".to_string());
                                func_param_ty_str
                            }
                            e => todo!("here: {e:?}")
                        }
                    }).collect::<Vec<_>>().join(", ");
                    let _ = write!(mod_name, "{}", args_str);
                }
                let _ = write!(mod_name, ")");
                analyzer.user_types().get(&mod_name).map(|idx| FunctionNode::from(*idx))
            }).collect()
        }
    }

    pub fn modifiers_as_base(&self) -> Vec<&Base> {
        self.attributes.iter().filter_map(|attr| {
            match attr {
                FunctionAttribute::BaseOrModifier(_, base) => Some(base),
                _ => None
            }
        }).collect()
    }
}

impl From<Function> for Node {
    fn from(val: Function) -> Self {
        Node::Function(val)
    }
}

impl From<FunctionDefinition> for Function {
    fn from(func: FunctionDefinition,) -> Function {
        Function {
            loc: func.loc,
            ty: func.ty,
            name: func.name,
            name_loc: func.name_loc,
            attributes: func.attributes,
            body: func.body,
            params: func.params,
            returns: func.returns,
        }
    }
}

impl From<VariableDefinition> for Function {
    fn from(var: VariableDefinition) -> Function {
        Function {
            loc: var.loc,
            ty: FunctionTy::Function,
            name: var.name.clone(),
            name_loc: var.loc,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Public(Some(var.loc)))],
            body: Some(Statement::Block {
                loc: var.loc,
                unchecked: false,
                statements: vec![
                    Statement::Return(
                        var.loc,
                        Some(Expression::Variable(var.name.expect("unnamed public variable?")))
                    )
                ]
            }),
            params: vec![],
            returns: vec![(var.loc, Some(Parameter { loc: var.loc, ty: var.ty, storage: None, name: None }))],
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

    pub fn ty_str(&self, analyzer: &'_ impl GraphLike) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty).expect("Non-typeable as type");
        var_ty.as_dot_str(analyzer)
    }

    pub fn ty(&self, analyzer: &'_ impl GraphLike) -> NodeIdx {
        self.underlying(analyzer).ty
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
    pub order: usize,
    pub storage: Option<StorageLocation>,
    pub name: Option<Identifier>,
}

impl From<FunctionParam> for Node {
    fn from(val: FunctionParam) -> Self {
        Node::FunctionParam(val)
    }
}

impl FunctionParam {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, param: Parameter, order: usize) -> Self {
        FunctionParam {
            loc: param.loc,
            ty: analyzer.parse_expr(&param.ty),
            order,
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
