use solang_parser::pt::Type;
use crate::analyzer::AsDotStr;
use crate::analyzer::Search;
use crate::context::{ContextEdge, ContextNode};
use crate::nodes::ContractNode;
use crate::range::SolcRange;
use crate::Edge;
use crate::VarType;
use crate::{
    analyzer::{AnalyzerLike, GraphLike},
    Node, NodeIdx,
};
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::ParameterList;
use solang_parser::pt::Statement;
use solang_parser::pt::VariableDefinition;
use solang_parser::pt::{
    Base, Expression, FunctionAttribute, FunctionDefinition, FunctionTy, Identifier, Loc,
    Parameter, StorageLocation, Visibility,
};
use std::collections::BTreeMap;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionNode(pub usize);
impl FunctionNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Function {
        match analyzer.node(*self) {
            Node::Function(func) => func,
            e => panic!("Node type confusion: expected node to be Function but it was: {e:?}"),
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
            .collect::<BTreeMap<_, _>>()
            .values()
            .copied()
            .collect()
    }

    pub fn modifiers_set(&self, analyzer: &impl GraphLike) -> bool {
        self.underlying(analyzer).modifiers_set
    }

    pub fn modifier_input_vars(
        &self,
        mod_num: usize,
        analyzer: &impl GraphLike,
    ) -> Vec<Expression> {
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
            e => panic!("Node type confusion: expected node to be Function but it was: {e:?}"),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        match self.underlying(analyzer).ty {
            FunctionTy::Constructor => format!(
                "constructor({})",
                self.params(analyzer)
                    .iter()
                    .map(|param| { param.ty_str(analyzer) })
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            FunctionTy::Receive => "receive()".to_string(),
            FunctionTy::Fallback => "fallback()".to_string(),
            _ => {
                self.underlying(analyzer)
                    .name
                    .clone()
                    .expect("Unnamed function")
                    .name
            }
        }
    }

    pub fn loc_specified_name(&self, analyzer: &'_ impl GraphLike) -> String {
        if let Some(con) = self.maybe_associated_contract(analyzer) {
            format!("{}.{}", con.name(analyzer), self.name(analyzer))
        } else {
            self.name(analyzer)
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

    pub fn maybe_associated_contract(&self, analyzer: &impl GraphLike) -> Option<ContractNode> {
        let parent = analyzer
            .search_for_ancestor_multi(self.0.into(), &[Edge::Func, Edge::Constructor, Edge::Modifier, Edge::ReceiveFunc, Edge::FallbackFunc])
            .unwrap_or_else(|| panic!("detached function: {:?}", self.name(analyzer)));
        match analyzer.node(parent) {
            Node::Contract(_) => Some(parent.into()),
            _ => None,
        }
    }

    pub fn associated_source_unit_part(&self, analyzer: &impl GraphLike) -> NodeIdx {
        let parent = analyzer
            .search_for_ancestor(self.0.into(), &Edge::Func)
            .expect("detached function");
        match analyzer.node(parent) {
            Node::Contract(_) => ContractNode::from(parent).associated_source_unit_part(analyzer),
            Node::SourceUnitPart(..) => parent,
            _ => panic!("detached function"),
        }
    }

    pub fn associated_source(&self, analyzer: &impl GraphLike) -> NodeIdx {
        analyzer
            .search_for_ancestor(self.associated_source_unit_part(analyzer), &Edge::Part)
            .expect("deatched function")
    }

    pub fn params(&self, analyzer: &'_ impl GraphLike) -> Vec<FunctionParamNode> {
        let mut params = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionParam == *edge.weight())
            .map(|edge| FunctionParamNode::from(edge.source()))
            .collect::<Vec<_>>();
        params.sort_by(|a, b| {
            a.underlying(analyzer)
                .order
                .cmp(&b.underlying(analyzer).order)
        });
        params
    }

    pub fn set_params_and_ret(
        &self,
        analyzer: &'_ mut (impl GraphLike + AnalyzerLike<Expr = Expression>),
    ) {
        let underlying = self.underlying(analyzer).clone();
        let mut params_strs = vec![];
        underlying
            .params
            .into_iter()
            .enumerate()
            .for_each(|(i, (_loc, input))| {
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

    pub fn returns(&self, analyzer: &'_ impl GraphLike) -> Vec<FunctionReturnNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::FunctionReturn == *edge.weight())
            .map(|edge| FunctionReturnNode::from(edge.source()))
            .collect()
    }

    pub fn is_public_or_ext(&self, analyzer: &'_ impl GraphLike) -> bool {
        self.underlying(analyzer).attributes.iter().any(|attr| {
            matches!(
                attr,
                FunctionAttribute::Visibility(Visibility::Public(_))
                    | FunctionAttribute::Visibility(Visibility::External(_))
            )
        })
    }

    pub fn get_overriding(&self, other: &Self, analyzer: &'_ impl GraphLike) -> Self {
        let self_attrs = &self.underlying(analyzer).attributes;
        let other_attrs = &other.underlying(analyzer).attributes;
        let self_virt_over_attr = self_attrs.iter().find(|attr| {
            // TODO: grab the override specifier if needed?
            matches!(attr, FunctionAttribute::Virtual(_) | FunctionAttribute::Override(_, _))
        });
        let other_virt_over_attr = other_attrs.iter().find(|attr| {
            // TODO: grab the override specifier if needed?
            matches!(attr, FunctionAttribute::Virtual(_) | FunctionAttribute::Override(_, _))
        });
        match (self_virt_over_attr, other_virt_over_attr) {
            (Some(FunctionAttribute::Virtual(_)), Some(FunctionAttribute::Virtual(_))) => *self,
            (Some(FunctionAttribute::Virtual(_)), Some(FunctionAttribute::Override(_, _))) => *other,
            (Some(FunctionAttribute::Override(_, _)), Some(FunctionAttribute::Virtual(_))) => *self,
            (Some(FunctionAttribute::Override(_, _)), Some(FunctionAttribute::Override(_, _))) => *self,
            (_, _) => *self
        }
    }
}

impl AsDotStr for FunctionNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let inputs = self
            .params(analyzer)
            .iter()
            .map(|param_node: &FunctionParamNode| param_node.as_dot_str(analyzer))
            .collect::<Vec<_>>()
            .join(", ");

        let attrs = self
            .underlying(analyzer)
            .attributes
            .iter()
            .map(|attr| match attr {
                FunctionAttribute::Mutability(inner) => format!("{inner}"),
                FunctionAttribute::Visibility(inner) => format!("{inner}"),
                FunctionAttribute::Virtual(_) => "virtual".to_string(),
                FunctionAttribute::Immutable(_) => "immutable".to_string(),
                FunctionAttribute::Override(_, _) => "override".to_string(),
                _ => "".to_string(),
            })
            .collect::<Vec<_>>()
            .join(" ");
        format!(
            "{} {}({}) {}",
            self.underlying(analyzer).ty,
            self.name(analyzer),
            inputs,
            attrs
        )
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
    pub modifiers_set: bool,
}

impl Default for Function {
    fn default() -> Self {
        Self {
            loc: Loc::Implicit,
            ty: FunctionTy::Function,
            name: None,
            name_loc: Loc::Implicit,
            attributes: vec![],
            body: None,
            params: vec![],
            returns: vec![],
            modifiers_set: false,
        }
    }
}

impl Function {
    pub fn modifiers_as_base(&self) -> Vec<&Base> {
        self.attributes
            .iter()
            .filter_map(|attr| match attr {
                FunctionAttribute::BaseOrModifier(_, base) => Some(base),
                _ => None,
            })
            .collect()
    }
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
            params: func.params,
            returns: func.returns,
            modifiers_set: false,
        }
    }
}


pub fn var_def_to_ret(expr: Expression) -> (Loc, Option<Parameter>) {
    match expr {
        Expression::Type(ty_loc, ref ty) => {
            match ty {
                Type::Mapping {
                    value: v_ty,
                    ..
                } => {
                    var_def_to_ret(*v_ty.clone())
                }
                Type::Address
                | Type::AddressPayable
                | Type::Payable
                | Type::Bool
                | Type::String
                | Type::Int(_)
                | Type::Uint(_)
                | Type::Bytes(_)
                | Type::Rational
                | Type::DynamicBytes => {
                    (ty_loc, Some(Parameter {
                        loc: ty_loc,
                        ty: expr,
                        storage: None,
                        name: None,
                    }))
                }
                e => panic!("Unsupported type: {e:?}")
            }
        }
        Expression::ArraySubscript(_loc, sub_expr, _) => {
            // its an array, add the index as a parameter
            var_def_to_ret(*sub_expr)
        }
        e => {
            (Loc::Implicit, Some(Parameter {
                loc: Loc::Implicit,
                ty: e,
                storage: None,
                name: None,
            }))
        }
    }
}
pub fn var_def_to_params(expr: Expression) -> Vec<(Loc, Option<Parameter>)> {
    let mut params = vec![];
    match expr {
        Expression::Type(ty_loc, ref ty) => {
            match ty {
                Type::Mapping {
                    loc,
                    key: key_ty,
                    value: v_ty,
                    ..
                } => {
                    params.push((ty_loc, Some(Parameter {
                        loc: *loc,
                        ty: *key_ty.clone(),
                        storage: None,
                        name: None,
                    })));
                    params.extend(var_def_to_params(*v_ty.clone()));
                }
                Type::Address
                | Type::AddressPayable
                | Type::Payable
                | Type::Bool
                | Type::String
                | Type::Int(_)
                | Type::Uint(_)
                | Type::Bytes(_)
                | Type::Rational
                | Type::DynamicBytes => {
                    // if !is_recursion {
                    //     params.push((ty_loc, Some(Parameter {
                    //         loc: ty_loc,
                    //         ty: expr,
                    //         storage: None,
                    //         name: None,
                    //     })));
                    // }
                }
                e => panic!("Unsupported type: {e:?}")
            }
        }
        Expression::ArraySubscript(loc, sub_expr, _) => {
            // its an array, add the index as a parameter
            params.push((loc, Some(Parameter {
                loc,
                ty: Expression::Type(loc, Type::Uint(256)),
                storage: None,
                name: None,
            })));
            params.extend(var_def_to_params(*sub_expr));
        }
        _e => {}
    }

    params
}

impl From<VariableDefinition> for Function {
    fn from(var: VariableDefinition) -> Function {
        let ret = var_def_to_ret(var.ty.clone());
        Function {
            loc: var.loc,
            ty: FunctionTy::Function,
            name: var.name.clone(),
            name_loc: var.loc,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Public(Some(
                var.loc,
            )))],
            body: None,
            params: var_def_to_params(var.ty),
            returns: vec![
                ret,
            ],
            modifiers_set: true,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionParamNode(pub usize);

impl AsDotStr for FunctionParamNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty)
            .expect("Non-typeable as type");
        format!(
            "{}{}{}",
            var_ty.as_dot_str(analyzer),
            if let Some(stor) = &self.underlying(analyzer).storage {
                format!(" {stor} ")
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
            e => panic!("Node type confusion: expected node to be FunctionParam but it was: {e:?}"),
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
        Some(self.underlying(analyzer).name.clone()?.name)
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
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty)
            .expect("Non-typeable as type");
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
    pub fn new(
        analyzer: &mut impl AnalyzerLike<Expr = Expression>,
        param: Parameter,
        order: usize,
    ) -> Self {
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
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).ty)
            .expect("Non-typeable as type");
        format!(
            "{}{}{}",
            var_ty.as_dot_str(analyzer),
            if let Some(stor) = &self.underlying(analyzer).storage {
                format!(" {stor} ")
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
            e => panic!("Node type confusion: expected node to be FunctionParam but it was: {e:?}"),
        }
    }

    pub fn maybe_name(&self, analyzer: &'_ impl GraphLike) -> Option<String> {
        Some(self.underlying(analyzer).name.clone()?.name)
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
