use crate::VarType;
use crate::analyzer::AsDotStr;
use crate::{analyzer::{GraphLike, AnalyzerLike}, Node, NodeIdx};
use solang_parser::pt::{Identifier, Loc, VariableAttribute, VariableDefinition, Expression, Visibility};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct VarNode(pub usize);

impl VarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Var {
        match analyzer.node(*self) {
            Node::Var(func) => func,
            e => panic!(
                "Node type confusion: expected node to be Var but it was: {:?}",
                e
            ),
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .clone()
            .expect("Unnamed function")
            .name
    }
}

impl AsDotStr for VarNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("{}{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer)
            } else {
                "".to_string()
            },
            underlying.attrs.iter().map(|attr| {
                match attr {
                    VariableAttribute::Visibility(vis) => format!(" {}", vis),
                    VariableAttribute::Constant(_) => " constant".to_string(),
                    VariableAttribute::Immutable(_) => " immutable".to_string(),
                    VariableAttribute::Override(_, _) => " override".to_string(),
                }
            }).collect::<Vec<_>>().join(" "),
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
        analyzer: &mut impl AnalyzerLike<Expr = Expression>,
        var: VariableDefinition,
        in_contract: bool,
    ) -> Var {
        Var {
            loc: var.loc,
            ty: analyzer.parse_expr(&var.ty),
            attrs: var.attrs,
            name: var.name,
            initializer: var.initializer.map(|init| analyzer.parse_expr(&init)),
            in_contract,
        }
    }

    pub fn is_public(&self) -> bool {
        self.attrs.iter().any(|var_attr| {
            matches!(var_attr, VariableAttribute::Visibility(Visibility::Public(_)))
        })
    }
}
