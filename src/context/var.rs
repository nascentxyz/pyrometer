use crate::{
    AnalyzerLike, ConcreteNode, ContextEdge, DynamicRangeSide, Edge, Field, FunctionParam,
    FunctionReturn, Node, NodeIdx, Op, Range, RangeElem, VarType,
};
use ethers_core::types::U256;
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

    pub fn display_name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer).display_name.clone()
    }

    pub fn range<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Range> {
        self.underlying(analyzer).ty.range(analyzer)
    }

    pub fn is_const(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).ty.is_const(analyzer)
    }

    pub fn is_tmp(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).is_tmp()
    }

    pub fn tmp_of(&self, analyzer: &impl AnalyzerLike) -> Option<TmpConstruction> {
        self.underlying(analyzer).tmp_of()
    }

    pub fn as_range_elem(
        &self,
        analyzer: &impl AnalyzerLike,
        range_side: DynamicRangeSide,
        loc: Loc,
    ) -> RangeElem {
        match self.underlying(analyzer).ty {
            VarType::Concrete(c) => {
                let val = c.underlying(analyzer).uint_val().expect("Not uint bound");
                RangeElem::Concrete(val, loc)
            }
            _ => RangeElem::Dynamic(self.0.into(), range_side, loc),
        }
    }

    pub fn set_range_min(&self, analyzer: &mut impl AnalyzerLike, new_min: RangeElem) {
        self.underlying_mut(analyzer).set_range_min(new_min)
    }

    pub fn set_range_max(&self, analyzer: &mut impl AnalyzerLike, new_max: RangeElem) {
        self.underlying_mut(analyzer).set_range_max(new_max)
    }

    pub fn latest_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn first_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Self {
        let mut earlier = *self;
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
        }
        earlier
    }

    pub fn next_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.source()))
            .take(1)
            .next()
    }

    pub fn previous_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn range_deps(&self, analyzer: &impl AnalyzerLike) -> Vec<Self> {
        if let Some(range) = self.range(analyzer) {
            range.dependent_on()
        } else {
            vec![]
        }
    }

    pub fn dependent_on(&self, analyzer: &impl AnalyzerLike, return_self: bool) -> Vec<Self> {
        let underlying = self.underlying(analyzer);
        if let Some(tmp) = underlying.tmp_of() {
            let mut nodes = tmp.lhs.dependent_on(analyzer, true);
            nodes.extend(tmp.rhs.dependent_on(analyzer, true));
            nodes
        } else if return_self {
            vec![*self]
        } else {
            vec![]
        }
    }

    pub fn is_concrete(&self, analyzer: &impl AnalyzerLike) -> bool {
        matches!(self.underlying(analyzer).ty, VarType::Concrete(_))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextVar {
    pub loc: Option<Loc>,
    pub name: String,
    pub display_name: String,
    pub storage: Option<StorageLocation>,
    pub tmp_of: Option<TmpConstruction>,
    pub ty: VarType,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TmpConstruction {
    pub lhs: ContextVarNode,
    pub op: Op,
    pub rhs: ContextVarNode,
}

impl TmpConstruction {
    pub fn new(lhs: ContextVarNode, op: Op, rhs: ContextVarNode) -> Self {
        Self { lhs, op, rhs }
    }
}

impl ContextVar {
    pub fn is_tmp(&self) -> bool {
        self.tmp_of.is_some()
    }

    pub fn tmp_of(&self) -> Option<TmpConstruction> {
        self.tmp_of
    }

    pub fn new_from_concrete(
        loc: Loc,
        concrete_node: ConcreteNode,
        analyzer: &impl AnalyzerLike,
    ) -> Self {
        ContextVar {
            loc: Some(loc),
            name: concrete_node.underlying(analyzer).as_string(),
            display_name: concrete_node.underlying(analyzer).as_string(),
            storage: None,
            tmp_of: None,
            ty: VarType::Concrete(concrete_node),
        }
    }

    pub fn set_range_min(&mut self, new_min: RangeElem) {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.min = new_min;
                } else {
                    *maybe_range = Some(Range {
                        min: new_min,
                        max: RangeElem::Concrete(U256::MAX, Loc::Implicit),
                    })
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {:?}", e),
        }
    }

    pub fn set_range_max(&mut self, new_max: RangeElem) {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.max = new_max;
                } else {
                    *maybe_range = Some(Range {
                        min: RangeElem::Concrete(U256::zero(), Loc::Implicit),
                        max: new_max,
                    })
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {:?}", e),
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
                name: parent_var.name.clone()
                    + "."
                    + &field.name.clone().expect("Field had no name").name,
                display_name: parent_var.name.clone()
                    + "."
                    + &field.name.expect("Field had no name").name,
                storage: parent_var.storage.clone(),
                tmp_of: None,
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
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: param.storage,
                    tmp_of: None,
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
                    name: name.name.clone(),
                    display_name: name.name,
                    storage: ret.storage,
                    tmp_of: None,
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
