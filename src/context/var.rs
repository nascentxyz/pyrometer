use crate::AnalyzerLike;
use crate::ConcreteNode;
use crate::ContextEdge;
use crate::Edge;
use crate::Field;
use crate::FunctionParam;
use crate::FunctionReturn;
use crate::Node;
use crate::NodeIdx;
use crate::Range;
use crate::VarType;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use solang_parser::pt::{Loc, StorageLocation};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ContextVarNode(pub usize);

impl Into<NodeIdx> for ContextVarNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

impl From<NodeIdx> for ContextVarNode {
    fn from(idx: NodeIdx) -> Self {
        ContextVarNode(idx.index())
    }
}

impl ContextVarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a ContextVar {
        match analyzer.node(*self) {
            Node::ContextVar(c) => c,
            e => panic!(
                "Node type confusion: expected node to be ContextVar but it was: {:?}",
                e
            ),
        }
    }

    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl AnalyzerLike) -> &'a mut ContextVar {
        match analyzer.node_mut(*self) {
            Node::ContextVar(c) => c,
            e => panic!(
                "Node type confusion: expected node to be ContextVar but it was: {:?}",
                e
            ),
        }
    }

    pub fn storage<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Option<StorageLocation> {
        &self.underlying(analyzer).storage
    }

    pub fn ty<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a VarType {
        &self.underlying(analyzer).ty
    }

    pub fn loc<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Loc {
        self.underlying(analyzer)
            .loc
            .expect("No loc for contextvar")
    }

    pub fn name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer).name.clone()
    }

    pub fn range<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Range> {
        self.underlying(analyzer).ty.range()
    }

    pub fn latest_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn first_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Self {
        println!("getting first version");
        let mut earlier = *self;
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
        }
        earlier
    }

    pub fn next_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::Next) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn previous_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Self> {
        // println!("getting previous version: {:?}", self.0);
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Next) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.source()))
            .take(1)
            .next()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextVar {
    pub loc: Option<Loc>,
    pub name: String,
    pub storage: Option<StorageLocation>,
    pub ty: VarType,
}

impl ContextVar {
    pub fn new_from_concrete(loc: Loc, tmp_var_ctr: usize, concrete_node: ConcreteNode) -> Self {
        ContextVar {
            loc: Some(loc),
            name: "$tmp_var_".to_string() + &tmp_var_ctr.to_string(),
            storage: None,
            ty: VarType::Concrete(concrete_node),
        }
    }

    pub fn maybe_new_from_field(
        analyzer: &impl AnalyzerLike,
        loc: Loc,
        parent_var: &ContextVar,
        field: Field,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, field.ty) {
            Some(ContextVar {
                loc: Some(loc),
                name: parent_var.name.clone() + "." + &field.name.expect("Field had no name").name,
                storage: parent_var.storage.clone(),
                ty,
            })
        } else {
            None
        }
    }
    pub fn maybe_new_from_func_param(
        analyzer: &impl AnalyzerLike,
        param: FunctionParam,
    ) -> Option<Self> {
        if let Some(name) = param.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, param.ty) {
                Some(ContextVar {
                    loc: Some(param.loc),
                    name: name.name,
                    storage: param.storage,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn maybe_new_from_func_ret(
        analyzer: &impl AnalyzerLike,
        ret: FunctionReturn,
    ) -> Option<Self> {
        if let Some(name) = ret.name {
            if let Some(ty) = VarType::try_from_idx(analyzer, ret.ty) {
                Some(ContextVar {
                    loc: Some(ret.loc),
                    name: name.name,
                    storage: ret.storage,
                    ty,
                })
            } else {
                None
            }
        } else {
            None
        }
    }
}
