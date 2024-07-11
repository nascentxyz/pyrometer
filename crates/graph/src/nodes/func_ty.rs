use crate::{
    nodes::{Concrete, ContextNode, ContractNode, SourceUnitNode, SourceUnitPartNode},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, ContextEdge, Edge, GraphBackend, Node, SolcRange, VarType,
};

use shared::{GraphError, NodeIdx, RangeArena, Search, StorageLocation};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::{
    helpers::CodeLocation,
    pt::{
        Base, Expression, FunctionAttribute, FunctionDefinition, FunctionTy, Identifier, Loc,
        Mutability, Parameter, ParameterList, Statement, Type, VariableDefinition, Visibility,
    },
};
use std::collections::BTreeMap;

pub enum FuncVis {
    Pure,
    View,
    Mut,
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionNode(pub usize);
impl FunctionNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Function, GraphError> {
        match analyzer.node(*self) {
            Node::Function(func) => Ok(func),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Function but it was: {e:?}"
            ))),
        }
    }

    pub fn add_gas_cost(
        &mut self,
        analyzer: &mut impl GraphBackend,
        cost: u64,
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.add_gas_cost(cost);
        Ok(())
    }

    pub fn ty(&self, analyzer: &impl GraphBackend) -> Result<FunctionTy, GraphError> {
        Ok(self.underlying(analyzer)?.ty)
    }

    pub fn is_constructor(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(self.ty(analyzer)?, FunctionTy::Constructor))
    }

    pub fn body_loc(&self, analyzer: &impl GraphBackend) -> Result<Option<Loc>, GraphError> {
        if let Some(body_stmt) = &self.underlying(analyzer)?.body {
            Ok(Some(body_stmt.loc()))
        } else {
            Ok(None)
        }
    }

    pub fn definition_loc(&self, analyzer: &impl GraphBackend) -> Result<Loc, GraphError> {
        let underlying = &self.underlying(analyzer)?;
        Ok(underlying.loc)
    }

    /// Gets an ordered list of modifiers for a given function
    pub fn modifiers(&self, analyzer: &mut impl AnalyzerBackend) -> Vec<FunctionNode> {
        if let Some(mods) = &self.underlying(analyzer).unwrap().cache.modifiers {
            mods.values().copied().collect()
        } else {
            let mods = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Incoming)
                .filter_map(|edge| {
                    if let Edge::FuncModifier(order) = *edge.weight() {
                        Some((order, FunctionNode::from(edge.source())))
                    } else {
                        None
                    }
                })
                .collect::<BTreeMap<_, _>>();
            self.underlying_mut(analyzer).unwrap().cache.modifiers = Some(mods.clone());
            mods.values().copied().collect()
        }
    }

    pub fn modifiers_set(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.modifiers_set)
    }

    pub fn modifier_input_vars(
        &self,
        mod_num: usize,
        analyzer: &impl GraphBackend,
    ) -> Result<Vec<Expression>, GraphError> {
        let modifiers = self.underlying(analyzer)?.modifiers_as_base();
        if let Some(modifier) = modifiers.get(mod_num) {
            if let Some(args) = &modifier.args {
                Ok(args.to_vec())
            } else {
                Ok(vec![])
            }
        } else {
            Ok(vec![])
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut Function, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Function(func) => Ok(func),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Function but it was: {e:?}"
            ))),
        }
    }

    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        match self.underlying(analyzer)?.ty {
            FunctionTy::Constructor => Ok(format!(
                "{}.constructor({})",
                self.maybe_slow_associated_contract(analyzer)
                    .unwrap()
                    .name(analyzer)
                    .unwrap(),
                self.params(analyzer)
                    .iter()
                    .map(|param| { param.ty_str(analyzer).unwrap() })
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
            FunctionTy::Receive => Ok(format!(
                "{}.receive()",
                self.maybe_slow_associated_contract(analyzer)
                    .unwrap()
                    .name(analyzer)
                    .unwrap()
            )),
            FunctionTy::Fallback => Ok(format!(
                "{}.fallback()",
                self.maybe_slow_associated_contract(analyzer)
                    .unwrap()
                    .name(analyzer)
                    .unwrap()
            )),
            _ => Ok(self
                .underlying(analyzer)?
                .name
                .clone()
                .expect("Unnamed function")
                .name),
        }
    }

    pub fn prefix_only_name(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<String>, GraphError> {
        match self.underlying(analyzer)?.ty {
            FunctionTy::Function => Ok(Some(
                self.underlying(analyzer)?
                    .name
                    .clone()
                    .expect("Unnamed function")
                    .name
                    .chars()
                    .take_while(|&ch| ch != '(')
                    .collect::<String>(),
            )),
            _ => Ok(None),
        }
    }

    pub fn loc_specified_name(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<String, GraphError> {
        if let Some(con) = self.maybe_associated_contract(analyzer) {
            Ok(format!("{}.{}", con.name(analyzer)?, self.name(analyzer)?))
        } else {
            self.name(analyzer)
        }
    }

    pub fn body_ctx(&self, analyzer: &mut impl AnalyzerBackend) -> ContextNode {
        if let Some(body_ctx) = self.underlying(analyzer).unwrap().cache.body_ctx {
            body_ctx
        } else {
            let body_ctx = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Incoming)
                .filter(|edge| Edge::Context(ContextEdge::Context) == *edge.weight())
                .map(|edge| ContextNode::from(edge.source()))
                .take(1)
                .next()
                .unwrap_or_else(|| {
                    panic!("No context for function: {}", self.name(analyzer).unwrap())
                });

            self.underlying_mut(analyzer).unwrap().cache.body_ctx = Some(body_ctx);
            body_ctx
        }
    }

    pub fn maybe_body_ctx(&self, analyzer: &mut impl AnalyzerBackend) -> Option<ContextNode> {
        if let Some(body_ctx) = self.underlying(analyzer).unwrap().cache.body_ctx {
            Some(body_ctx)
        } else {
            let body_ctx = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Incoming)
                .filter(|edge| Edge::Context(ContextEdge::Context) == *edge.weight())
                .map(|edge| ContextNode::from(edge.source()))
                .take(1)
                .next();
            if let Some(b) = body_ctx {
                self.underlying_mut(analyzer).unwrap().cache.body_ctx = Some(b);
            }

            body_ctx
        }
    }

    pub fn maybe_slow_associated_contract(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Option<ContractNode> {
        if let Some(maybe_contract) = self
            .underlying(analyzer)
            .unwrap()
            .cache
            .maybe_associated_contract
        {
            maybe_contract
        } else {
            let contract = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| {
                    matches!(
                        *edge.weight(),
                        Edge::Func
                            | Edge::Modifier
                            | Edge::Constructor
                            | Edge::ReceiveFunc
                            | Edge::FallbackFunc
                    )
                })
                .filter_map(|edge| {
                    let node = edge.target();
                    match analyzer.node(node) {
                        Node::Contract(_) => Some(ContractNode::from(node)),
                        _ => None,
                    }
                })
                .take(1)
                .next();
            contract
        }
    }

    pub fn maybe_associated_contract(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Option<ContractNode> {
        if let Some(maybe_contract) = self
            .underlying(analyzer)
            .unwrap()
            .cache
            .maybe_associated_contract
        {
            maybe_contract
        } else {
            let contract = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| {
                    matches!(
                        *edge.weight(),
                        Edge::Func
                            | Edge::Modifier
                            | Edge::Constructor
                            | Edge::ReceiveFunc
                            | Edge::FallbackFunc
                    )
                })
                .filter_map(|edge| {
                    let node = edge.target();
                    match analyzer.node(node) {
                        Node::Contract(_) => Some(ContractNode::from(node)),
                        _ => None,
                    }
                })
                .take(1)
                .next();
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .maybe_associated_contract = Some(contract);
            contract
        }
    }

    pub fn maybe_associated_source_unit_part(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Option<SourceUnitPartNode> {
        if let Some(sup) = self
            .underlying(analyzer)
            .unwrap()
            .cache
            .associated_source_unit_part
        {
            Some(sup.into())
        } else {
            let parent = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| {
                    matches!(
                        *edge.weight(),
                        Edge::Func
                            | Edge::Modifier
                            | Edge::Constructor
                            | Edge::ReceiveFunc
                            | Edge::FallbackFunc
                    )
                })
                .map(|edge| edge.target())
                .take(1)
                .next()?;
            let sup = match analyzer.node(parent) {
                Node::Contract(_) => {
                    ContractNode::from(parent).associated_source_unit_part(analyzer)
                }
                Node::SourceUnitPart(..) => parent.into(),
                _e => return None,
            };
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .associated_source_unit_part = Some(sup.into());
            Some(sup)
        }
    }

    pub fn associated_source(&self, analyzer: &mut impl AnalyzerBackend) -> SourceUnitNode {
        if let Some(src) = self.underlying(analyzer).unwrap().cache.associated_source {
            src.into()
        } else {
            let sup = self
                .maybe_associated_source_unit_part(analyzer)
                .expect("No associated source unit part");
            let src = analyzer
                .search_for_ancestor(sup.into(), &Edge::Part)
                .expect("detached function");
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .associated_source = Some(src);
            src.into()
        }
    }

    pub fn maybe_associated_source(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Option<SourceUnitNode> {
        if let Some(src) = self.underlying(analyzer).unwrap().cache.associated_source {
            Some(src.into())
        } else {
            let sup = self.maybe_associated_source_unit_part(analyzer)?;
            let src = analyzer.search_for_ancestor(sup.into(), &Edge::Part)?;
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .associated_source = Some(src);
            Some(src.into())
        }
    }

    pub fn params(&self, analyzer: &impl GraphBackend) -> Vec<FunctionParamNode> {
        if let Some(params) = &self.underlying(analyzer).unwrap().cache.params {
            params.to_vec()
        } else {
            let mut params = analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Incoming)
                .filter(|edge| Edge::FunctionParam == *edge.weight())
                .map(|edge| FunctionParamNode::from(edge.source()))
                .collect::<Vec<_>>();
            params.sort_by(|a, b| {
                a.underlying(analyzer)
                    .unwrap()
                    .order
                    .cmp(&b.underlying(analyzer).unwrap().order)
            });
            params
        }
    }

    pub fn ordered_param_names(&self, analyzer: &impl GraphBackend) -> Vec<String> {
        let param_nodes = self.params(analyzer);
        param_nodes
            .iter()
            .map(|i| i.name(analyzer).unwrap())
            .collect()
    }

    pub fn maybe_ordered_param_names(&self, analyzer: &impl GraphBackend) -> Option<Vec<String>> {
        let param_nodes = self.params(analyzer);
        let names: Vec<String> = param_nodes
            .iter()
            .filter_map(|i| i.maybe_name(analyzer).unwrap())
            .collect();
        if names.len() == param_nodes.len() {
            Some(names)
        } else {
            None
        }
    }

    pub fn set_params_and_ret(
        &self,
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let underlying = self.underlying(analyzer)?.clone();
        let mut params_strs = vec![];
        let params = underlying
            .params
            .into_iter()
            .enumerate()
            .filter_map(|(i, (_loc, input))| {
                if let Some(input) = input {
                    let param = FunctionParam::new(analyzer, arena, input, i);
                    let input_node = analyzer.add_node(param);
                    params_strs.push(
                        FunctionParamNode::from(input_node)
                            .ty_str(analyzer)
                            .unwrap(),
                    );
                    analyzer.add_edge(input_node, *self, Edge::FunctionParam);
                    Some(input_node.into())
                } else {
                    None
                }
            })
            .collect();
        let rets = underlying
            .returns
            .into_iter()
            .filter_map(|(_loc, output)| {
                if let Some(output) = output {
                    let ret = FunctionReturn::new(analyzer, arena, output);
                    let output_node = analyzer.add_node(ret);
                    analyzer.add_edge(output_node, *self, Edge::FunctionReturn);
                    Some(output_node.into())
                } else {
                    None
                }
            })
            .collect();

        let underlying_mut = self.underlying_mut(analyzer)?;
        if let Some(ref mut name) = underlying_mut.name {
            name.name = format!("{}({})", name.name, params_strs.join(", "));
        }
        underlying_mut.cache.params = Some(params);
        underlying_mut.cache.returns = Some(rets);
        Ok(())
    }

    // fn returns_inner(
    //     &self,
    //     analyzer: &impl GraphBackend,
    // ) -> Vec<FunctionReturnNode> {
    //     self.underlying(analyzer).unwrap().cache.returns.iter()
    //     // } else {
    //     //     analyzer
    //     //         .graph()
    //     //         .edges_directed(self.0.into(), Direction::Incoming)
    //     //         .filter(|edge| Edge::FunctionReturn == *edge.weight())
    //     //         .map(|edge| FunctionReturnNode::from(edge.source()))
    //     //         .collect()
    //     // }
    // }

    pub fn returns(
        &self,
        arena: &mut RangeArena<Elem<Concrete>>,
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
    ) -> Vec<FunctionReturnNode> {
        if let Some(cached) = self.underlying(analyzer).unwrap().cache.returns.as_ref() {
            cached.to_vec()
        } else {
            let underlying = self.underlying(analyzer).unwrap().clone();
            let rets = underlying
                .returns
                .into_iter()
                .filter_map(|(_loc, output)| {
                    if let Some(output) = output {
                        let ret = FunctionReturn::new(analyzer, arena, output);
                        let output_node = analyzer.add_node(ret);
                        analyzer.add_edge(output_node, *self, Edge::FunctionReturn);
                        Some(output_node.into())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            let underlying_mut = self.underlying_mut(analyzer).unwrap();
            underlying_mut.cache.returns = Some(rets.clone());
            rets
        }
    }

    pub fn is_public_or_ext(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.attributes.iter().any(|attr| {
            matches!(
                attr,
                FunctionAttribute::Visibility(Visibility::Public(_))
                    | FunctionAttribute::Visibility(Visibility::External(_))
            )
        }))
    }

    pub fn is_pure(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .attributes
            .iter()
            .any(|attr| matches!(attr, FunctionAttribute::Mutability(Mutability::Pure(_)))))
    }

    pub fn is_view(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .attributes
            .iter()
            .any(|attr| matches!(attr, FunctionAttribute::Mutability(Mutability::View(_)))))
    }

    pub fn visibility(&self, analyzer: &impl GraphBackend) -> Result<FuncVis, GraphError> {
        if self.is_pure(analyzer)? {
            Ok(FuncVis::Pure)
        } else if self.is_view(analyzer)? {
            Ok(FuncVis::View)
        } else {
            Ok(FuncVis::Mut)
        }
    }

    pub fn get_overriding(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
    ) -> Result<Self, GraphError> {
        let self_attrs = &self.underlying(analyzer)?.attributes;
        let other_attrs = &other.underlying(analyzer)?.attributes;
        let self_virt_over_attr = self_attrs.iter().find(|attr| {
            // TODO: grab the override specifier if needed?
            matches!(
                attr,
                FunctionAttribute::Virtual(_) | FunctionAttribute::Override(_, _)
            )
        });
        let other_virt_over_attr = other_attrs.iter().find(|attr| {
            // TODO: grab the override specifier if needed?
            matches!(
                attr,
                FunctionAttribute::Virtual(_) | FunctionAttribute::Override(_, _)
            )
        });
        match (self_virt_over_attr, other_virt_over_attr) {
            (Some(FunctionAttribute::Virtual(_)), Some(FunctionAttribute::Virtual(_))) => Ok(*self),
            (Some(FunctionAttribute::Virtual(_)), Some(FunctionAttribute::Override(_, _))) => {
                Ok(*other)
            }
            (Some(FunctionAttribute::Override(_, _)), Some(FunctionAttribute::Virtual(_))) => {
                Ok(*self)
            }
            (Some(FunctionAttribute::Override(_, _)), Some(FunctionAttribute::Override(_, _))) => {
                Ok(*self)
            }
            (_, _) => Ok(*self),
        }
    }
}

impl AsDotStr for FunctionNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let inputs = self
            .params(analyzer)
            .iter()
            .map(|param_node: &FunctionParamNode| param_node.as_dot_str(analyzer, arena))
            .collect::<Vec<_>>()
            .join(", ");

        let attrs = self
            .underlying(analyzer)
            .unwrap()
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
            "{} {}({}) {} -- gas: {}",
            self.underlying(analyzer).unwrap().ty,
            self.name(analyzer).unwrap().split('(').collect::<Vec<_>>()[0],
            inputs,
            attrs,
            self.underlying(analyzer).unwrap().estimated_gas
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
    pub cache: FunctionCache,
    pub estimated_gas: u64,
}

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct FunctionCache {
    pub returns: Option<Vec<FunctionReturnNode>>,
    pub params: Option<Vec<FunctionParamNode>>,
    pub body_ctx: Option<ContextNode>,
    pub modifiers: Option<BTreeMap<usize, FunctionNode>>,
    pub maybe_associated_contract: Option<Option<ContractNode>>,
    pub associated_source: Option<NodeIdx>,
    pub associated_source_unit_part: Option<NodeIdx>,
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
            cache: Default::default(),
            estimated_gas: 0,
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

    pub fn add_gas_cost(&mut self, cost: u64) {
        self.estimated_gas += cost;
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
            cache: Default::default(),
            estimated_gas: 0,
        }
    }
}

pub fn var_def_to_ret(expr: Expression) -> (Loc, Option<Parameter>) {
    match expr {
        Expression::Type(ty_loc, ref ty) => match ty {
            Type::Mapping { value: v_ty, .. } => var_def_to_ret(*v_ty.clone()),
            Type::Address
            | Type::AddressPayable
            | Type::Payable
            | Type::Bool
            | Type::String
            | Type::Int(_)
            | Type::Uint(_)
            | Type::Bytes(_)
            | Type::Rational
            | Type::DynamicBytes => (
                ty_loc,
                Some(Parameter {
                    loc: ty_loc,
                    ty: expr,
                    storage: None,
                    name: None,
                }),
            ),
            e => panic!("Unsupported type: {e:?}"),
        },
        Expression::ArraySubscript(_loc, sub_expr, _) => {
            // its an array, add the index as a parameter
            var_def_to_ret(*sub_expr)
        }
        e => (
            Loc::Implicit,
            Some(Parameter {
                loc: Loc::Implicit,
                ty: e,
                storage: None,
                name: None,
            }),
        ),
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
                    params.push((
                        ty_loc,
                        Some(Parameter {
                            loc: *loc,
                            ty: *key_ty.clone(),
                            storage: None,
                            name: None,
                        }),
                    ));
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
                e => panic!("Unsupported type: {e:?}"),
            }
        }
        Expression::ArraySubscript(loc, sub_expr, _) => {
            // its an array, add the index as a parameter
            params.push((
                loc,
                Some(Parameter {
                    loc,
                    ty: Expression::Type(loc, Type::Uint(256)),
                    storage: None,
                    name: None,
                }),
            ));
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
            returns: vec![ret],
            modifiers_set: true,
            cache: Default::default(),
            estimated_gas: 0,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionParamNode(pub usize);

impl AsDotStr for FunctionParamNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).unwrap().ty)
            .expect("Non-typeable as type");
        format!(
            "{}{}{}",
            var_ty.as_dot_str(analyzer, arena),
            if let Some(stor) = &self.underlying(analyzer).unwrap().storage {
                format!(" {stor} ")
            } else {
                " ".to_string()
            },
            if let Some(name) = self.maybe_name(analyzer).unwrap() {
                name
            } else {
                "".to_string()
            }
        )
    }
}

impl FunctionParamNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a FunctionParam, GraphError> {
        match analyzer.node(*self) {
            Node::FunctionParam(param) => Ok(param),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be FunctionParam but it was: {e:?}"
            ))),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphBackend) -> Result<String, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .name
            .clone()
            .expect("Unnamed function parameter")
            .name)
    }

    pub fn maybe_name(&self, analyzer: &impl GraphBackend) -> Result<Option<String>, GraphError> {
        if let Some(ident) = self.underlying(analyzer)?.name.clone() {
            Ok(Some(ident.name))
        } else {
            Ok(None)
        }
    }

    pub fn range(&self, analyzer: &impl GraphBackend) -> Result<Option<SolcRange>, GraphError> {
        let ty_node = self.underlying(analyzer)?.ty;
        if let Some(var_ty) = VarType::try_from_idx(analyzer, ty_node) {
            Ok(var_ty.range(analyzer)?)
        } else {
            Ok(None)
        }
    }

    pub fn loc(&self, analyzer: &impl GraphBackend) -> Result<Loc, GraphError> {
        Ok(self.underlying(analyzer)?.loc)
    }

    pub fn ty_str(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer)?.ty).ok_or(
            GraphError::NodeConfusion("Non-typeable as type".to_string()),
        )?;
        var_ty.as_string(analyzer)
    }

    pub fn ty(&self, analyzer: &impl GraphBackend) -> Result<NodeIdx, GraphError> {
        Ok(self.underlying(analyzer)?.ty)
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
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
        param: Parameter,
        order: usize,
    ) -> Self {
        FunctionParam {
            loc: param.loc,
            ty: analyzer.parse_expr(arena, &param.ty, None),
            order,
            storage: param.storage.map(|s| s.into()),
            name: param.name,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FunctionReturnNode(pub usize);

impl AsDotStr for FunctionReturnNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let var_ty = VarType::try_from_idx(analyzer, self.underlying(analyzer).unwrap().ty)
            .expect("Non-typeable as type");
        format!(
            "{}{}{}",
            var_ty.as_dot_str(analyzer, arena),
            if let Some(stor) = &self.underlying(analyzer).unwrap().storage {
                format!(" {stor} ")
            } else {
                " ".to_string()
            },
            if let Some(name) = self.maybe_name(analyzer).unwrap() {
                name
            } else {
                "".to_string()
            }
        )
    }
}

impl FunctionReturnNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a FunctionReturn, GraphError> {
        match analyzer.node(*self) {
            Node::FunctionReturn(ret) => Ok(ret),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be FunctionReturn but it was: {e:?}"
            ))),
        }
    }

    pub fn maybe_name(&self, analyzer: &impl GraphBackend) -> Result<Option<String>, GraphError> {
        if let Some(ident) = self.underlying(analyzer)?.name.clone() {
            Ok(Some(ident.name))
        } else {
            Ok(None)
        }
    }

    pub fn loc(&self, analyzer: &impl GraphBackend) -> Result<Loc, GraphError> {
        Ok(self.underlying(analyzer)?.loc)
    }

    pub fn ty(&self, analyzer: &impl GraphBackend) -> Result<NodeIdx, GraphError> {
        Ok(self.underlying(analyzer)?.ty)
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
    pub fn new(
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
        param: Parameter,
    ) -> Self {
        FunctionReturn {
            loc: param.loc,
            ty: analyzer.parse_expr(arena, &param.ty, None),
            storage: param.storage.map(|s| s.into()),
            name: param.name,
        }
    }
}
