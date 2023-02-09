use crate::GraphLike;
use petgraph::{Direction, visit::EdgeRef};
use crate::analyzer::AsDotStr;
use crate::VarType;
use crate::analyzer::AnalyzerLike;
use crate::Node;
use crate::Edge;
use crate::NodeIdx;
use solang_parser::pt::{Identifier, Loc, StructDefinition, VariableDeclaration, Expression};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct StructNode(pub usize);

impl StructNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Struct {
        match analyzer.node(*self) {
            Node::Struct(st) => st,
            e => panic!(
                "Node type confusion: expected node to be Struct but it was: {:?}",
                e
            ),
        }
    }

    pub fn loc(&self, analyzer: &impl GraphLike) -> Loc {
        Struct::maybe_from_node(analyzer.node(*self).clone())
            .expect("Node wasnt struct")
            .loc
    }

    pub fn name(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .as_ref()
            .expect("Struct wasn't named")
            .to_string()
    }

    pub fn fields(&self, analyzer: &impl GraphLike) -> Vec<FieldNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Field == *edge.weight())
            .map(|edge| FieldNode::from(edge.source()))
            .collect()
    }
}


impl AsDotStr for StructNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("struct {} {{ {} }}",
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            },
            self.fields(analyzer).iter().map(|field_node| {
                field_node.as_dot_str(analyzer)
            }).collect::<Vec<_>>().join("; ")
        )
    }
}

impl From<StructNode> for NodeIdx {
    fn from(val: StructNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for StructNode {
    fn from(idx: NodeIdx) -> Self {
        StructNode(idx.index())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Struct {
    pub loc: Loc,
    pub name: Option<Identifier>,
}

impl Struct {
    pub fn maybe_from_node(node: Node) -> Option<Self> {
        match node {
            Node::Struct(s) => Some(s),
            _ => None,
        }
    }
}

impl From<Struct> for Node {
    fn from(val: Struct) -> Self {
        Node::Struct(val)
    }
}

impl From<StructDefinition> for Struct {
    fn from(con: StructDefinition) -> Struct {
        Struct {
            loc: con.loc,
            name: con.name,
        }
    }
}

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct FieldNode(pub usize);

impl FieldNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Field {
        match analyzer.node(*self) {
            Node::Field(field) => field,
            e => panic!(
                "Node type confusion: expected node to be Field but it was: {:?}",
                e
            ),
        }
    }

    pub fn name(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer)
            .name
            .as_ref()
            .expect("Struct wasn't named")
            .to_string()
    }
}

impl AsDotStr for FieldNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);
        format!("{} {}",
            if let Some(var_ty) = VarType::try_from_idx(analyzer, underlying.ty) {
                var_ty.as_dot_str(analyzer)
            } else {
                "".to_string()
            },
            if let Some(name) = &underlying.name {
                name.name.clone()
            } else {
                "".to_string()
            }
        )
    }
}

impl From<NodeIdx> for FieldNode {
    fn from(idx: NodeIdx) -> Self {
        FieldNode(idx.index())
    }
}

impl From<FieldNode> for NodeIdx {
    fn from(val: FieldNode) -> Self {
        val.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Field {
    pub loc: Loc,
    pub ty: NodeIdx,
    pub name: Option<Identifier>,
}

impl From<Field> for Node {
    fn from(val: Field) -> Self {
        Node::Field(val)
    }
}

impl Field {
    pub fn new(analyzer: &mut impl AnalyzerLike<Expr = Expression>, var_def: VariableDeclaration) -> Field {
        let ty_idx = analyzer.parse_expr(&var_def.ty);
        Field {
            loc: var_def.loc,
            ty: ty_idx,
            name: var_def.name,
        }
    }
}
