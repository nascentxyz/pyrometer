use crate::AnalyzerLike;
use crate::Builtin;
use crate::ContractNode;
use crate::TypeNode;
use crate::BuiltInNode;
use crate::GraphLike;
use crate::range::range_string::ToRangeString;
use crate::AsDotStr;
use crate::range::elem_ty::Dynamic;
use crate::range::elem_ty::RangeConcrete;
use crate::range::Range;
use crate::Concrete;
use crate::range::elem_ty::Elem;
use crate::range::SolcRange;
use crate::{
    analyzer::{Search},
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
impl AsDotStr for ContextVarNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        let underlying = self.underlying(analyzer);

        let range_str = if let Some(r) = underlying.ty.range(analyzer) {
            format!("[{}, {}]", r.evaled_range_min(analyzer).to_range_string(false, analyzer).s, r.evaled_range_max(analyzer).to_range_string(true, analyzer).s)
        } else {
            "".to_string()
        };

        format!("{} -- {} -- range: {}", underlying.display_name, underlying.ty.as_string(analyzer), range_str)
    }
}

impl From<ContextVarNode> for NodeIdx {
    fn from(val: ContextVarNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextVarNode {
    fn from(idx: NodeIdx) -> Self {
        ContextVarNode(idx.index())
    }
}

impl ContextVarNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a ContextVar {
        match analyzer.node(*self) {
            Node::ContextVar(c) => c,
            e => panic!(
                "Node type confusion: expected node to be ContextVar but it was: {:?}",
                e
            ),
        }
    }

    pub fn underlying_mut<'a>(&self, analyzer: &'a mut impl GraphLike) -> &'a mut ContextVar {
        match analyzer.node_mut(*self) {
            Node::ContextVar(c) => c,
            e => panic!(
                "Node type confusion: expected node to be ContextVar but it was: {:?}",
                e
            ),
        }
    }

    pub fn storage<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Option<StorageLocation> {
        &self.underlying(analyzer).storage
    }

    pub fn is_storage(&self, analyzer: &impl GraphLike) -> bool {
        matches!(self.underlying(analyzer).storage, Some(StorageLocation::Storage(..)))
    }

    pub fn ty<'a>(&self, analyzer: &'a impl GraphLike) -> &'a VarType {
        &self.underlying(analyzer).ty
    }

    pub fn loc(&self, analyzer: &'_ impl GraphLike) -> Loc {
        self.underlying(analyzer)
            .loc
            .expect("No loc for contextvar")
    }

    pub fn ctx(&self, analyzer: &'_ (impl GraphLike + Search)) -> ContextNode {
        ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()
                .expect("No associated ctx"),
        )
    }

    pub fn maybe_ctx(&self, analyzer: &'_ (impl GraphLike + Search)) -> Option<ContextNode> {
        Some(ContextNode::from(
            analyzer
                .search_for_ancestor(self.0.into(), &Edge::Context(ContextEdge::Variable))
                .into_iter()
                .take(1)
                .next()?,
        ))
    }

    pub fn update_deps(&mut self, ctx: ContextNode, analyzer: &mut (impl GraphLike + AnalyzerLike)) {
        if let Some(mut range) = self.range(analyzer) {
            range.update_deps(ctx, analyzer);
            self.set_range_min(analyzer, range.min);
            self.set_range_max(analyzer, range.max);
        }
    }

    pub fn name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer).name.clone()
    }

    pub fn display_name(&self, analyzer: &'_ impl GraphLike) -> String {
        self.underlying(analyzer).display_name.clone()
    }

    pub fn range(&self, analyzer: &'_ impl GraphLike) -> Option<SolcRange> {
        self.underlying(analyzer).ty.range(analyzer)
    }

    pub fn range_min(&self, analyzer: &'_ impl GraphLike) -> Option<Elem<Concrete>> {
        Some(self.range(analyzer)?.range_min())
    }

    pub fn range_max(&self, analyzer: &'_ impl GraphLike) -> Option<Elem<Concrete>> {
        Some(self.range(analyzer)?.range_max())
    }

    pub fn evaled_range_min(&self, analyzer: &'_ impl GraphLike) -> Option<Elem<Concrete>> {
        Some(self.range(analyzer)?.evaled_range_min(analyzer))
    }

    pub fn evaled_range_max(&self, analyzer: &'_ impl GraphLike) -> Option<Elem<Concrete>> {
        Some(self.range(analyzer)?.evaled_range_max(analyzer))
    }

    pub fn is_const(&self, analyzer: &impl GraphLike) -> bool {
        let underlying = self.underlying(analyzer);
        underlying.storage.is_none() && underlying.ty.is_const(analyzer)
    }

    pub fn is_symbolic(&self, analyzer: &impl GraphLike) -> bool {
        self.underlying(analyzer).is_symbolic
    }

    pub fn is_tmp(&self, analyzer: &impl GraphLike) -> bool {
        let underlying = self.underlying(analyzer);
        
        // println!("is tmp: {}, {}", underlying.display_name, is);
        underlying.is_tmp()
    }

    pub fn is_return_node(&self, analyzer: &impl GraphLike) -> bool {
        if let Some(ctx) = self.maybe_ctx(analyzer) {
            return ctx.underlying(analyzer).ret.iter().any(|(_, node)| node.name(analyzer) == self.name(analyzer));
        }
        false
    }

    pub fn is_return_node_in_any(&self, ctxs: &[ContextNode], analyzer: &impl GraphLike) -> bool {
        ctxs.iter().any(|ctx| ctx.underlying(analyzer).ret.iter().any(|(_, node)| node.name(analyzer) == self.name(analyzer)))
    }

    pub fn tmp_of(&self, analyzer: &impl GraphLike) -> Option<TmpConstruction> {
        self.underlying(analyzer).tmp_of()
    }

    pub fn is_len_var(&self, analyzer: &impl GraphLike) -> bool {
        self.name(analyzer).ends_with(".length")
            && analyzer.search_for_ancestor(self.first_version(analyzer).into(), &Edge::Context(ContextEdge::AttrAccess))
                .is_some()
    }

    pub fn is_array_index_access(&self, analyzer: &impl GraphLike) -> bool {
        analyzer.search_for_ancestor(self.first_version(analyzer).into(), &Edge::Context(ContextEdge::IndexAccess))
                .is_some()
    }

    pub fn len_var_to_array(&self, analyzer: &impl GraphLike) -> Option<ContextVarNode> {
        if self.name(analyzer).ends_with(".length") {
            let arr = analyzer.search_for_ancestor(self.first_version(analyzer).into(), &Edge::Context(ContextEdge::AttrAccess))?;
            Some(ContextVarNode::from(arr).latest_version(analyzer))
        } else {
            None
        }
    }

    pub fn index_to_array(&self, analyzer: &impl GraphLike) -> Option<ContextVarNode> {
        let arr = analyzer.search_for_ancestor(self.first_version(analyzer).into(), &Edge::Context(ContextEdge::IndexAccess))?;
        Some(ContextVarNode::from(arr).latest_version(analyzer))
    }

    pub fn index_access_to_index(&self, analyzer: &impl GraphLike) -> Option<ContextVarNode> {
        let set = analyzer.search_children(self.first_version(analyzer).into(), &Edge::Context(ContextEdge::Index));
        let index = set.first()?;
        Some(ContextVarNode::from(*index))
    }

    pub fn as_range_elem(
        &self,
        analyzer: &impl GraphLike,
        loc: Loc,
    ) -> Elem<Concrete> {
        match self.underlying(analyzer).ty {
            VarType::Concrete(c) => {
                Elem::Concrete(RangeConcrete { val: c.underlying(analyzer).clone(), loc })
            }
            _ => Elem::Dynamic(Dynamic { idx: self.0.into(), loc }),
        }
    }

    pub fn set_range_min(&self, analyzer: &mut (impl GraphLike + AnalyzerLike), new_min: Elem<Concrete>) {
        if self.is_concrete(analyzer) {
            let mut new_ty = self.ty(analyzer).clone();
            new_ty.concrete_to_builtin(analyzer);
            self.underlying_mut(analyzer).ty = new_ty;
            self.set_range_min(analyzer, new_min);
        } else {
            let fallback = self.underlying(analyzer).fallback_range(analyzer);
            self.underlying_mut(analyzer)
                .set_range_min(new_min, fallback);
        }
    }

    pub fn set_range_max(&self, analyzer: &mut (impl GraphLike + AnalyzerLike), new_max: Elem<Concrete>) {
        if self.is_concrete(analyzer) {
            let mut new_ty = self.ty(analyzer).clone();
            new_ty.concrete_to_builtin(analyzer);
            self.underlying_mut(analyzer).ty = new_ty;
            self.set_range_max(analyzer, new_max);
        } else {
            let fallback = self.underlying(analyzer).fallback_range(analyzer);
            self.underlying_mut(analyzer)
                .set_range_max(new_max, fallback)
        }
    }

    pub fn set_range_exclusions(&self, analyzer: &mut impl GraphLike, new_exclusions: Vec<Elem<Concrete>>) {
        let fallback = self.underlying(analyzer).fallback_range(analyzer);
        self.underlying_mut(analyzer)
            .set_range_exclusions(new_exclusions, fallback);
    }

    pub fn try_set_range_min(&self, analyzer: &mut (impl GraphLike + AnalyzerLike), new_min: Elem<Concrete>) -> bool {
        if self.is_concrete(analyzer) {
            let mut new_ty = self.ty(analyzer).clone();
            new_ty.concrete_to_builtin(analyzer);
            self.underlying_mut(analyzer).ty = new_ty;
            self.try_set_range_min(analyzer, new_min)
        } else {
            let fallback = self.underlying(analyzer).fallback_range(analyzer);
            self.underlying_mut(analyzer)
                .try_set_range_min(new_min, fallback)
        }
    }

    pub fn try_set_range_max(&self, analyzer: &mut (impl GraphLike + AnalyzerLike), new_max: Elem<Concrete>) -> bool {
        if self.is_concrete(analyzer) {
            let mut new_ty = self.ty(analyzer).clone();
            new_ty.concrete_to_builtin(analyzer);
            self.underlying_mut(analyzer).ty = new_ty;
            self.try_set_range_max(analyzer, new_max)
        } else {
            let fallback = self.underlying(analyzer).fallback_range(analyzer);
            self.underlying_mut(analyzer)
                .try_set_range_max(new_max, fallback)
        }
    }

    pub fn try_set_range_exclusions(&self, analyzer: &mut impl GraphLike, new_exclusions: Vec<Elem<Concrete>>) -> bool {
        let fallback = self.underlying(analyzer).fallback_range(analyzer);
        self.underlying_mut(analyzer)
            .try_set_range_exclusions(new_exclusions, fallback)
    }

    pub fn latest_version(&self, analyzer: &'_ impl GraphLike) -> Self {
        let mut latest = *self;
        while let Some(next) = latest.next_version(analyzer) {
            latest = next;
        }
        latest
    }

    pub fn latest_version_less_than(&self, idx: NodeIdx, analyzer: &'_ impl GraphLike) -> Self {
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

    pub fn latest_version_in_ctx(&self, ctx: ContextNode, analyzer: &'_ impl GraphLike) -> Self {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)) {
            cvar.latest_version(analyzer)
        } else {
            *self
        }
    }

    pub fn latest_version_in_ctx_less_than(&self, idx: NodeIdx, ctx: ContextNode, analyzer: &'_ impl GraphLike) -> Self {
        if let Some(cvar) = ctx.var_by_name(analyzer, &self.name(analyzer)) {
            cvar.latest_version_less_than(idx, analyzer)
        } else {
            *self
        }
    }

    pub fn first_version(&self, analyzer: &'_ impl GraphLike) -> Self {
        let mut earlier = *self;
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
        }
        earlier
    }

    pub fn num_versions(&self, analyzer: &'_ impl GraphLike) -> usize {
        let mut count = 1;
        let mut earlier = self.latest_version(analyzer);
        while let Some(prev) = earlier.previous_version(analyzer) {
            earlier = prev;
            count += 1;
        }
        count
    }

    pub fn next_version(&self, analyzer: &'_ impl GraphLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.source()))
            .take(1)
            .next()
    }

    pub fn previous_version(&self, analyzer: &'_ impl GraphLike) -> Option<Self> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| Edge::Context(ContextEdge::Prev) == *edge.weight())
            .map(|edge| ContextVarNode::from(edge.target()))
            .take(1)
            .next()
    }

    pub fn range_deps(&self, analyzer: &impl GraphLike) -> Vec<Self> {
        if let Some(range) = self.range(analyzer) {
            range.dependent_on()
        } else {
            vec![]
        }
    }

    pub fn dependent_on(&self, analyzer: &impl GraphLike, return_self: bool) -> Vec<Self> {
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

    pub fn is_concrete(&self, analyzer: &impl GraphLike) -> bool {
        matches!(self.underlying(analyzer).ty, VarType::Concrete(_))
    }

    pub fn as_concrete(&self, analyzer: &impl GraphLike) -> Concrete {
        match &self.underlying(analyzer).ty {
            VarType::Concrete(c) => c.underlying(analyzer).clone(),
            e => panic!("Was not concrete: {e:?}"),
        }
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Self {
        let new_underlying = self.underlying(analyzer).clone().as_cast_tmp(loc, ctx, cast_ty, analyzer);
        analyzer.add_node(Node::ContextVar(new_underlying)).into()
    }

    pub fn ty_eq(
        &self,
        other: &Self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> bool {
        self.ty(analyzer).ty_eq(other.ty(analyzer), analyzer)
    }

    pub fn cast_from(
        &self,
        other: &Self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        let to_ty = other.ty(analyzer).clone();
        self.cast_from_ty(to_ty, analyzer);
    }

    pub fn cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        let from_ty = self.ty(analyzer).clone();
        if !from_ty.ty_eq(&to_ty, analyzer) {
            if let Some(new_ty) = from_ty.try_cast(&to_ty, analyzer) {
                self.underlying_mut(analyzer).ty = new_ty;
            }
            if let (Some(r), Some(r2)) = (self.range(analyzer), to_ty.range(analyzer)) {
                let min = r.min.cast(r2.min);
                let max = r.max.cast(r2.max);
                self.set_range_min(analyzer, min);
                self.set_range_max(analyzer, max);
            }
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer), to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer).as_string();
            self.underlying_mut(analyzer).display_name = display_name;
        }
    }

    pub fn try_increase_size(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        let from_ty = self.ty(analyzer).clone();
        self.cast_from_ty(from_ty.max_size(analyzer), analyzer);
    }

    pub fn is_int(&self, analyzer: &impl GraphLike) -> bool {
        self.underlying(analyzer).ty.is_int(analyzer)
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
    pub is_symbolic: bool,
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
        analyzer: &impl GraphLike,
    ) -> Self {
        ContextVar {
            loc: Some(loc),
            name: concrete_node.underlying(analyzer).as_string(),
            display_name: concrete_node.underlying(analyzer).as_string(),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            ty: VarType::Concrete(concrete_node),
        }
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Self {
        let mut new_tmp = self.clone();
        new_tmp.loc = Some(loc);
        new_tmp.is_tmp = true;
        new_tmp.name = format!("tmp{}_{}({}({}))", self.name, ctx.new_tmp(analyzer), cast_ty.as_string(analyzer), self.name);
        new_tmp
    }

    pub fn new_from_contract(
        loc: Loc,
        contract_node: ContractNode,
        analyzer: &impl GraphLike,
    ) -> Self {
        ContextVar {
            loc: Some(loc),
            name: contract_node.name(analyzer),
            display_name: contract_node.name(analyzer),
            storage: None,
            is_tmp: false,
            tmp_of: None,
            is_symbolic: true,
            ty: VarType::User(TypeNode::Contract(contract_node)),
        }
    }

    pub fn new_from_builtin(
        loc: Loc,
        bn_node: BuiltInNode,
        analyzer: &impl GraphLike,
    ) -> Self {
        ContextVar {
            loc: Some(loc),
            name: bn_node.underlying(analyzer).as_string(analyzer),
            display_name: bn_node.underlying(analyzer).as_string(analyzer),
            storage: None,
            is_tmp: true,
            tmp_of: None,
            is_symbolic: false,
            ty: VarType::try_from_idx(analyzer, bn_node.into()).unwrap(),
        }
    }

    pub fn fallback_range(&self, analyzer: &impl GraphLike) -> Option<SolcRange> {
        match &self.ty {
            VarType::BuiltIn(bn, ref maybe_range) => {
                if let Some(range) = maybe_range {
                    Some(range.clone())
                } else {
                    let underlying = bn.underlying(analyzer);
                    SolcRange::try_from_builtin(underlying)
                }
            }
            VarType::Concrete(cn) => SolcRange::from(cn.underlying(analyzer).clone()),
            _ => None,
        }
    }

    pub fn set_range_min(&mut self, new_min: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::BuiltIn(_, ref mut maybe_range) => {
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

    pub fn try_set_range_min(&mut self, new_min: Elem<Concrete>, fallback_range: Option<SolcRange>) -> bool {
        match &mut self.ty {
            VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_min(new_min);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_min(new_min);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => { true }
            _ => false,
        }
    }

    pub fn set_range_max(&mut self, new_max: Elem<Concrete>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::BuiltIn(_, ref mut maybe_range) => {
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

    pub fn set_range_exclusions(&mut self, new_exclusions: Vec<Elem<Concrete>>, fallback_range: Option<SolcRange>) {
        match &mut self.ty {
            VarType::BuiltIn(_, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                }
            }
            VarType::Concrete(_) => {}
            e => panic!("wasnt builtin or concrete: {:?}", e),
        }
    }

    pub fn try_set_range_max(&mut self, new_max: Elem<Concrete>, fallback_range: Option<SolcRange>) -> bool {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_max(new_max);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_max(new_max);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => { true }
            _ => false,
        }
    }

    pub fn try_set_range_exclusions(&mut self, new_exclusions: Vec<Elem<Concrete>>, fallback_range: Option<SolcRange>) -> bool {
        match &mut self.ty {
            VarType::BuiltIn(_bn, ref mut maybe_range) => {
                if let Some(range) = maybe_range {
                    range.set_range_exclusions(new_exclusions);
                    true
                } else {
                    let mut fr = fallback_range.expect("No range and no fallback_range");
                    fr.set_range_exclusions(new_exclusions);
                    *maybe_range = Some(fr);
                    true
                }
            }
            VarType::Concrete(_) => { true }
            _ => false,
        }
    }

    pub fn maybe_from_user_ty(
        analyzer: &impl GraphLike,
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
                        if !var.attrs.iter().any(|attr| matches!(attr, solang_parser::pt::VariableAttribute::Constant(_))) {
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
                storage,
                is_tmp: false,
                tmp_of: None,
                is_symbolic: true,
                ty,
            })
        } else {
            None
        }
    }

    pub fn maybe_new_from_field(
        analyzer: &impl GraphLike,
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
                is_symbolic: true,
                ty,
            })
        } else {
            None
        }
    }

    pub fn new_from_index(
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        loc: Loc,
        parent_name: String,
        parent_display_name: String,
        parent_storage: StorageLocation,
        parent_var: &BuiltInNode,
        index: ContextVarNode,
    ) -> Self {
       ContextVar {
            loc: Some(loc),
            name: parent_name
                + "["
                + &index.name(analyzer)
                + "]",
            display_name: parent_display_name
                + "["
                + &index.display_name(analyzer)
                + "]",
            storage: Some(parent_storage),
            is_tmp: false,
            tmp_of: None,
            is_symbolic: index.underlying(analyzer).is_symbolic,
            ty: parent_var.array_underlying_ty(analyzer),
        }
    }

    pub fn maybe_new_from_func_param(
        analyzer: &impl GraphLike,
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
                    is_symbolic: true,
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
        analyzer: &impl GraphLike,
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
                    is_symbolic: true,
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
