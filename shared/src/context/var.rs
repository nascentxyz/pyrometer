use crate::range::elem_ty::Dynamic;
use crate::range::elem_ty::DynSide;
use crate::range::elem_ty::RangeConcrete;
use crate::range::Range;
use crate::Concrete;
use crate::range::elem_ty::Elem;
use crate::range::SolcRange;
use crate::{
    analyzer::{AnalyzerLike, Search},
    context::ContextNode,
    range::elem::RangeOp,
    nodes::ConcreteNode, ContextEdge, Edge, Field, FunctionParam, FunctionReturn, Node,
    NodeIdx, VarType,
};

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

    pub fn ctx<'a>(&self, analyzer: &'a (impl AnalyzerLike + Search)) -> ContextNode {
        ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()
                .expect("No associated ctx"),
        )
    }

    pub fn maybe_ctx<'a>(&self, analyzer: &'a (impl AnalyzerLike + Search)) -> Option<ContextNode> {
        Some(ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()?,
        ))
    }

    pub fn update_deps(&mut self, ctx: ContextNode, analyzer: &mut impl AnalyzerLike) {
        if let Some(mut range) = self.range(analyzer) {
            range.update_deps(ctx, analyzer);
            self.set_range_min(analyzer, range.min);
            self.set_range_max(analyzer, range.max);
        }
    }

    pub fn name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer).name.clone()
    }

    pub fn display_name<'a>(&self, analyzer: &'a impl AnalyzerLike) -> String {
        self.underlying(analyzer).display_name.clone()
    }

    pub fn range<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Option<SolcRange> {
        match &self.underlying(analyzer).ty {
            VarType::BuiltIn(_bn, Some(r)) => Some(r.clone()),
            VarType::BuiltIn(bn, None) => SolcRange::try_from_builtin(bn.underlying(analyzer)),
            VarType::Concrete(cn) => SolcRange::from(cn.underlying(analyzer).clone()),
            _ => None,
        }
    }

    pub fn is_const(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).ty.is_const(analyzer)
    }

    pub fn is_symbolic(&self, analyzer: &impl AnalyzerLike) -> bool {
        self.underlying(analyzer).ty.is_symbolic(analyzer)
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
        range_side: DynSide,
        loc: Loc,
    ) -> Elem<Concrete> {
        match self.underlying(analyzer).ty {
            VarType::Concrete(c) => {
                Elem::Concrete(RangeConcrete { val: c.underlying(analyzer).clone(), loc })
            }
            _ => Elem::Dynamic(Dynamic { idx: self.0.into(), side: range_side, loc }),
        }
    }

    pub fn set_range_min(&self, analyzer: &mut impl AnalyzerLike, new_min: Elem<Concrete>) {
        let fallback = self.underlying(analyzer).fallback_range(analyzer);
        self.underlying_mut(analyzer)
            .set_range_min(new_min, fallback);
    }

    pub fn set_range_max(&self, analyzer: &mut impl AnalyzerLike, new_max: Elem<Concrete>) {
        let fallback = self.underlying(analyzer).fallback_range(analyzer);
        self.underlying_mut(analyzer)
            .set_range_max(new_max, fallback)
    }

    pub fn latest_version<'a>(&self, analyzer: &'a impl AnalyzerLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn latest_version_less_than<'a>(&self, idx: NodeIdx, analyzer: &'a impl AnalyzerLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            if next.0 <= idx.index() {
                latest = next;
            } else {
                break;
            }
        }
        latest
    }

    pub fn latest_version_in_ctx<'a>(&self, ctx: ContextNode, analyzer: &'a impl AnalyzerLike) -> Self {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)) {
            cvar.latest_version(analyzer)
        } else {
            *self
        }
    }

    pub fn latest_version_in_ctx_less_than<'a>(&self, idx: NodeIdx, ctx: ContextNode, analyzer: &'a impl AnalyzerLike) -> Self {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)) {
            cvar.latest_version_less_than(idx, analyzer)
        } else {
            *self
        }
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
            if let Some(rhs) = tmp.rhs {
                nodes.extend(rhs.dependent_on(analyzer, true));
            }
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
    pub is_tmp: bool,
    pub tmp_of: Option<TmpConstruction>,
    pub ty: VarType,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TmpConstruction {
    pub lhs: ContextVarNode,
    pub op: RangeOp,
    pub rhs: Option<ContextVarNode>,
}

impl TmpConstruction {
    pub fn new(lhs: ContextVarNode, op: RangeOp, rhs: Option<ContextVarNode>) -> Self {
        Self { lhs, op, rhs }
    }
}

impl ContextVar {
    pub fn is_tmp(&self) -> bool {
        self.is_tmp || self.tmp_of.is_some()
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
            is_tmp: true,
            tmp_of: None,
            ty: VarType::Concrete(concrete_node),
        }
    }

    pub fn fallback_range(&self, analyzer: &impl AnalyzerLike) -> Option<SolcRange> {
        match &self.ty {
            VarType::BuiltIn(bn, ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Some(range.clone())
                } else {
                    let underlying = bn.underlying(analyzer);
                    println!("fallback range buitlin: {:?}", underlying);
                    if let Some(range) = SolcRange::try_from_builtin(underlying) {
                        Some(range)
                    } else {
                        None
                    }
                }
            }
            VarType::Concrete(cn) => SolcRange::from(cn.underlying(analyzer).clone()),
            e => panic!("wasnt builtin: {:?}", e),
        }
    }

    pub fn set_range_min(&mut self, new_min: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin: {:?}", e),
        }
    }

    pub fn set_range_max(&mut self, new_max: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {:?}", e),
        }
    }

    pub fn maybe_from_user_ty(
        analyzer: &impl AnalyzerLike,
        loc: Loc,
        node_idx: NodeIdx,
    ) -> Option<Self> {
        if let Some(ty) = VarType::try_from_idx(analyzer, node_idx) {
            let (name, storage) = match analyzer.node(node_idx) {
                Node::Contract(c) => {
                    let name = c.name.clone().expect("Contract had no name").name;
                    (name, None)
                }
                Node::Function(f) => {
                    let name = f.name.clone().expect("Function had no name").name;
                    (name, None)
                }
                Node::Struct(s) => {
                    let name = s.name.clone().expect("Struct had no name").name;
                    (name, None)
                }
                Node::Enum(e) => {
                    let name = e.name.clone().expect("Enum had no name").name;
                    (name, None)
                }
                Node::Var(var) => {
                    let name = var.name.clone().expect("Variable had no name").name;
                    let storage = if var.in_contract {
                        if !var.attrs.iter().any(|attr| match attr {
                            solang_parser::pt::VariableAttribute::Constant(_) => true,
                            _ => false,
                        }) {
                            Some(StorageLocation::Storage(var.loc))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    (name, storage)
                }
                Node::Ty(ty) => {
                    let name = &ty.name.name;
                    (name.clone(), None)
                }
                _ => return None,
            };

            Some(ContextVar {
                loc: Some(loc),
                name: name.clone(),
                display_name: name,
                storage: storage,
                is_tmp: false,
                tmp_of: None,
                ty,
            })
        } else {
            None
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
                is_tmp: false,
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
                    is_tmp: false,
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
                    is_tmp: false,
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
