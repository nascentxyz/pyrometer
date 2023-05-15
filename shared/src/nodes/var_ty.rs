use crate::nodes::GraphError;
use crate::ContextVar;
use crate::ContextVarNode;
use crate::VarType;
use crate::{
    analyzer::{AnalyzerLike, AsDotStr, GraphLike},
    Node, NodeIdx,
};
use solang_parser::pt::{
    Expression, Identifier, Loc, VariableAttribute, VariableDefinition, Visibility,
};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarNode(pub usize);

impl VarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Var, GraphError> {
        match analyzer.node(*self) {
            Node::Var(func) => Ok(func),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Var but it was: {e:?}"
            ))),
        }
    }

    pub fn name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
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
        analyzer: &impl GraphLike,
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
}

impl AsDotStr for VarNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer).unwrap();
        format!(
            "{}{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer)
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
    pub in_contract: bool,
}

impl From<Var> for Node {
    fn from(val: Var) -> Self {
        Node::Var(val)
    }
}

impl Var {
    pub fn new(
        analyzer: &mut (impl GraphLike + AnalyzerLike<Expr = Expression>),
        var: VariableDefinition,
        in_contract: bool,
    ) -> Var {
        let ty = analyzer.parse_expr(&var.ty);
        let is_const = var
            .attrs
            .iter()
            .any(|attr| matches!(attr, VariableAttribute::Constant(_)));
        Var {
            loc: var.loc,
            ty,
            attrs: var.attrs,
            name: var.name,
            initializer: var.initializer.and_then(|init| {
                // we only evaluate this if the variable is constant
                if is_const {
                    let init = analyzer.parse_expr(&init);
                    if let Node::ContextVar(_) = analyzer.node(init) {
                        let v_ty = VarType::try_from_idx(analyzer, ty).unwrap();
                        ContextVarNode::from(init).cast_from_ty(v_ty, analyzer).expect("Could not cast right hand side initializer to specified left hand side for variable");
                        Some(init)
                    } else {
                        Some(init)
                    }
                } else {
                    None
                }
            }),
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
