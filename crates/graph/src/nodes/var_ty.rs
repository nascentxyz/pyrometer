use crate::{
    nodes::{
        Concrete, ContextVar, ContextVarNode, ContractNode, SourceUnitNode, SourceUnitPartNode,
    },
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, ContextEdge, Edge, GraphBackend, Node, VarType,
};

use shared::{GraphError, NodeIdx, RangeArena, Search};

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::{
    Expression, Identifier, Loc, VariableAttribute, VariableDefinition, Visibility,
};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarNode(pub usize);

impl VarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Var, GraphError> {
        match analyzer.node(*self) {
            Node::Var(func) => Ok(func),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Var but it was: {e:?}"
            ))),
        }
    }

    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut Var, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Var(func) => Ok(func),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Var but it was: {e:?}"
            ))),
        }
    }

    pub fn parse_initializer(
        &self,
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
        parent: NodeIdx,
    ) -> Result<(), GraphError> {
        if let Some(expr) = self.underlying(analyzer)?.initializer_expr.clone() {
            tracing::trace!(
                "Parsing variable initializer for {}",
                self.underlying(analyzer)?.name.as_ref().unwrap().name
            );
            let init = analyzer.parse_expr(arena, &expr, Some(parent));

            let underlying = self.underlying(analyzer)?.clone();
            let mut set = false;
            if let Some(ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                if let Some(initer) = VarType::try_from_idx(analyzer, init) {
                    if let Some(initer) = initer.try_cast(&ty, analyzer)? {
                        if let Some(conc_idx) = initer.builtin_to_concrete_idx(analyzer, arena)? {
                            set = true;
                            self.underlying_mut(analyzer)?.initializer = Some(conc_idx);
                        }
                    }
                }
            }

            if !set {
                self.underlying_mut(analyzer)?.initializer = Some(init);
            }
        }
        Ok(())
    }

    pub fn maybe_associated_contract(&self, analyzer: &impl GraphBackend) -> Option<ContractNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| matches!(*edge.weight(), Edge::Var))
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

    pub fn maybe_associated_source_unit_part(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Option<SourceUnitPartNode> {
        if let Some(con) = self.maybe_associated_contract(analyzer) {
            Some(con.associated_source_unit_part(analyzer))
        } else {
            analyzer
                .graph()
                .edges_directed(self.0.into(), Direction::Outgoing)
                .filter(|edge| matches!(*edge.weight(), Edge::Var))
                .filter_map(|edge| {
                    let node = edge.target();
                    match analyzer.node(node) {
                        Node::SourceUnitPart(..) => Some(node.into()),
                        _ => None,
                    }
                })
                .take(1)
                .next()
        }
    }

    pub fn maybe_associated_source(
        &self,
        analyzer: &(impl GraphBackend + Search),
    ) -> Option<SourceUnitNode> {
        let sup = self.maybe_associated_source_unit_part(analyzer)?;
        analyzer
            .search_for_ancestor(sup.into(), &Edge::Part)
            .map(Into::into)
    }

    pub fn name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .name
            .clone()
            .expect("Unnamed function")
            .name)
    }

    pub fn const_value(
        &self,
        loc: Loc,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<ContextVar>, GraphError> {
        let attrs = &self.underlying(analyzer)?.attrs;
        if attrs
            .iter()
            .any(|attr| matches!(attr, VariableAttribute::Constant(_)))
        {
            if let Some(init) = self.underlying(analyzer)?.initializer {
                if let Some(ty) = VarType::try_from_idx(analyzer, init) {
                    return Ok(Some(ContextVar {
                        loc: Some(loc),
                        name: self.name(analyzer)?,
                        display_name: self.name(analyzer)?,
                        storage: None,
                        is_tmp: false,
                        dep_on: None,
                        tmp_of: None,
                        is_symbolic: true,
                        is_return: false,
                        ty,
                    }));
                }
            }
        }
        Ok(None)
    }

    pub fn inherited_into(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| {
                matches!(
                    *edge.weight(),
                    Edge::Context(ContextEdge::InheritedStorageVariable)
                )
            })
            .map(|edge| ContextVarNode::from(edge.source()))
            .collect()
    }

    pub fn reconstruct_src<'a>(
        &self,
        analyzer: &'a impl AnalyzerBackend,
    ) -> Result<&'a str, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        Ok(&analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()])
    }
}

impl AsDotStr for VarNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "{}{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer, arena)
            } else {
                "".to_string()
            },
            underlying
                .attrs
                .iter()
                .map(|attr| {
                    match attr {
                        VariableAttribute::Visibility(vis) => format!(" {vis}"),
                        VariableAttribute::Constant(_) => " constant".to_string(),
                        VariableAttribute::Immutable(_) => " immutable".to_string(),
                        VariableAttribute::Override(_, _) => " override".to_string(),
                    }
                })
                .collect::<Vec<_>>()
                .join(" "),
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            }
        )
    }
}

impl From<VarNode> for NodeIdx {
    fn from(val: VarNode) -> Self {
        val.0.into()
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
    pub initializer_expr: Option<Expression>,
    pub in_contract: bool,
}

impl From<Var> for Node {
    fn from(val: Var) -> Self {
        Node::Var(val)
    }
}

impl Var {
    pub fn new(
        analyzer: &mut impl AnalyzerBackend<Expr = Expression>,
        arena: &mut RangeArena<Elem<Concrete>>,
        var: VariableDefinition,
        in_contract: bool,
    ) -> Var {
        tracing::trace!("Parsing Var type");
        let ty = analyzer.parse_expr(arena, &var.ty, None);
        Var {
            loc: var.loc,
            ty,
            attrs: var.attrs,
            name: var.name,
            initializer: None,
            initializer_expr: var.initializer,
            in_contract,
        }
    }

    pub fn is_public(&self) -> bool {
        self.attrs.iter().any(|var_attr| {
            matches!(
                var_attr,
                VariableAttribute::Visibility(Visibility::Public(_))
            )
        })
    }
}
