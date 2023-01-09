use crate::AnalyzerLike;
use crate::Concrete;
use crate::ContextEdge;
use crate::ContextNode;
use crate::ContextVarNode;
use crate::Edge;
use crate::Node;
use crate::NodeIdx;
use crate::Range;
use crate::RangeElem;
use crate::RangeElemString;
use crate::RangeString;
use crate::VarType;
use ariadne::{Color, ColorGenerator, Label, Report, ReportKind, Source, Span};
use petgraph::graph::Edges;
use petgraph::visit::EdgeRef;
use petgraph::{graph::*, Directed, Direction};
use solang_parser::pt::Loc;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Copy, Clone)]
pub enum Relative {
    Eq,
    Lt,
    Lte,
    Gt,
    Gte,
}

impl ToString for Relative {
    fn to_string(&self) -> String {
        use Relative::*;
        match self {
            Eq => "==".to_string(),
            Lt => "<".to_string(),
            Lte => "<=".to_string(),
            Gt => ">".to_string(),
            Gte => ">=".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Analysis {
    Relative(Relative, RangeElem),
}

impl Analysis {
    pub fn relative_string(&self) -> String {
        match self {
            Analysis::Relative(rel, _) => rel.to_string(),
        }
    }

    pub fn target_var_def(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
            Analysis::Relative(_, target) => target.def_string(analyzer),
        }
    }

    pub fn relative_target_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
            Analysis::Relative(_, target) => target.to_range_string(analyzer),
        }
    }

    pub fn relative_target_bounds_string(&self, analyzer: &impl AnalyzerLike) -> Vec<RangeString> {
        match self {
            Analysis::Relative(_, target) => target.bounds_range_string(analyzer),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ArrayAccess {
    MinSize,
    MaxSize,
}

#[derive(Debug, Clone)]
pub struct ArrayAccessAnalysis {
    pub arr_def: ContextVarNode,
    pub arr_loc: LocSpan,
    pub def_loc: LocSpan,
    pub access_loc: LocSpan,
    pub analysis: Analysis,
    pub analysis_ty: ArrayAccess,
}

#[derive(Debug, Copy, Clone)]
pub struct LocSpan(pub Loc);

impl Span for LocSpan {
    type SourceId = usize;
    fn source(&self) -> &Self::SourceId {
        match self.0 {
            Loc::File(ref f, _, _) => f,
            Loc::Implicit => &0,
            _ => todo!("handle non file loc"),
        }
    }

    fn start(&self) -> usize {
        match self.0 {
            Loc::File(_, start, _) => start,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }

    fn end(&self) -> usize {
        match self.0 {
            Loc::File(_, _, end) => end,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }
}

pub trait ReportDisplay {
    fn report_kind(&self) -> ReportKind;
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String;
    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>>;
    fn report(&self, analyzer: &(impl AnalyzerLike + Search)) -> Report<LocSpan>;
    fn print_report(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search));
}

impl ReportDisplay for ArrayAccessAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Advice
    }
    fn msg(&self, analyzer: &impl AnalyzerLike) -> String {
        match self.analysis_ty {
            ArrayAccess::MinSize => format!(
                "Minimum array length: length must be {} {}",
                self.analysis.relative_string(),
                self.analysis.relative_target_string(analyzer).s,
            ),
            ArrayAccess::MaxSize => "Maximum array length: length must be {}{}".to_string(),
        }
    }
    fn labels(&self, analyzer: &impl AnalyzerLike) -> Vec<Label<LocSpan>> {
        let primary_def = self.analysis.target_var_def(analyzer);
        let mut labels = self
            .analysis
            .relative_target_bounds_string(analyzer)
            .into_iter()
            .flat_map(|range_string| {
                let mut labels = vec![];
                match (range_string.min.loc, range_string.max.loc) {
                    (Loc::Implicit, Loc::Implicit) => labels,
                    (Loc::Implicit, _) => {
                        labels.push(
                            Label::new(LocSpan(range_string.max.loc))
                                .with_message(range_string.min.s + " to " + &range_string.max.s)
                                .with_color(Color::Cyan),
                        );
                        labels
                    }
                    (_, Loc::Implicit) => {
                        labels.push(
                            Label::new(LocSpan(range_string.min.loc))
                                .with_message(range_string.min.s + " to " + &range_string.max.s)
                                .with_color(Color::Cyan),
                        );
                        labels
                    }
                    (_, _) => {
                        labels.push(
                            Label::new(LocSpan(range_string.min.loc))
                                .with_message(range_string.min.s.clone() + " to ..")
                                .with_color(Color::Cyan),
                        );
                        labels.push(
                            Label::new(LocSpan(range_string.max.loc))
                                .with_message(range_string.min.s + " to " + &range_string.max.s)
                                .with_color(Color::Cyan),
                        );
                        labels
                    }
                }
            })
            .collect::<Vec<_>>();

        labels.extend([
            Label::new(self.arr_loc)
                .with_message("Array accessed here")
                .with_color(Color::Green),
            Label::new(self.def_loc)
                .with_message("Length enforced by this")
                .with_color(Color::Red),
        ]);

        if primary_def.loc != Loc::Implicit {
            labels.push(
                Label::new(LocSpan(primary_def.loc))
                    .with_message(primary_def.s + " <- Index access defined here"),
            );
        }

        labels
    }
    fn report(&self, analyzer: &(impl AnalyzerLike + Search)) -> Report<LocSpan> {
        let mut report = Report::build(
            self.report_kind(),
            *self.arr_loc.source(),
            self.arr_loc.start(),
        )
        .with_message(self.msg(analyzer));

        for label in self.labels(analyzer).into_iter() {
            report = report.with_label(label);
        }

        report.finish()
    }
    fn print_report(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let report = self.report(analyzer);
        report.print((src.0, Source::from(src.1))).unwrap()
    }
}

pub trait ContextAnalyzer: AnalyzerLike + Search + ArrayAccessAnalyzer {}

pub trait Search: AnalyzerLike {
    fn search_for_ancestor(&self, start: NodeIdx, edge_ty: &Edge) -> Option<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Outgoing);
        if let Some(edge) = edges.clone().find(|edge| edge.weight() == edge_ty) {
            Some(edge.target())
        } else {
            edges
                .map(|edge| edge.target())
                .filter_map(|node| self.search_for_ancestor(node, edge_ty))
                .take(1)
                .next()
        }
    }
    /// Finds any child nodes that have some edge `edge_ty` incoming. Builds up a set of these
    ///
    /// i.e.: a -my_edge-> b -other_edge-> c -my_edge-> d
    ///
    /// This function would build a set { b, d } if we are looking for `my_edge` and start at a.
    fn search_children(&self, start: NodeIdx, edge_ty: &Edge) -> BTreeSet<NodeIdx> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        this_children.extend(
            edges
                .flat_map(|edge| self.search_children(edge.source(), edge_ty))
                .collect::<BTreeSet<NodeIdx>>(),
        );
        this_children
    }

    /// Finds any child nodes that have some edge `edge_ty` incoming. Builds up a mapping of these
    ///
    /// i.e.: a -my_edge-> b -other_edge-> c -my_edge-> d
    ///
    /// This function would build a map { a: [b], c: [d] } if we are looking for `my_edge` and start at a.
    fn nodes_with_children(
        &self,
        start: NodeIdx,
        edge_ty: &Edge,
    ) -> Option<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>> {
        let edges = self.graph().edges_directed(start, Direction::Incoming);
        let mut map: BTreeMap<NodeIdx, BTreeSet<NodeIdx>> = Default::default();

        let this_children: BTreeSet<NodeIdx> = edges
            .clone()
            .filter_map(|edge| {
                if edge.weight() == edge_ty {
                    Some(edge.source())
                } else {
                    None
                }
            })
            .collect();

        if !this_children.is_empty() {
            map.insert(start, this_children);
        }
        map.extend(
            edges
                .filter_map(|edge| self.nodes_with_children(edge.source(), edge_ty))
                .flatten()
                .collect::<BTreeMap<NodeIdx, BTreeSet<NodeIdx>>>(),
        );
        if map.is_empty() {
            None
        } else {
            Some(map)
        }
    }
}

pub trait ArrayAccessAnalyzer: Search + AnalyzerLike + Sized {
    fn min_size_to_prevent_access_revert(&self, ctx: ContextNode) -> Vec<ArrayAccessAnalysis> {
        let mut analyses = Default::default();

        if let Some(arrays) =
            self.nodes_with_children(ctx.into(), &Edge::Context(ContextEdge::IndexAccess))
        {
            analyses = arrays
                .iter()
                .flat_map(|(array, accesses)| {
                    accesses
                        .iter()
                        .map(|access| {
                            let cvar_idx = *self
                                .search_children(*access, &Edge::Context(ContextEdge::Index))
                                .iter()
                                .take(1)
                                .next()
                                .expect("IndexAccess without Index");
                            let def = ContextVarNode::from(cvar_idx)
                                .first_version(self)
                                .underlying(self);
                            let cvar = ContextVarNode::from(cvar_idx).underlying(self);
                            match &cvar.ty {
                                VarType::Concrete(conc_node) => {
                                    // its a concrete index, the analysis should be a Gt the concrete value
                                    match conc_node.underlying(self) {
                                        Concrete::Uint(_, val) => ArrayAccessAnalysis {
                                            arr_def: ContextVarNode::from(*array),
                                            arr_loc: LocSpan(
                                                ContextVarNode::from(*array).loc(self),
                                            ),
                                            def_loc: LocSpan(def.loc.expect("No loc for access")),
                                            access_loc: LocSpan(
                                                cvar.loc.expect("No loc for access"),
                                            ),
                                            analysis: Analysis::Relative(
                                                Relative::Gt,
                                                RangeElem::Concrete(
                                                    *val,
                                                    cvar.loc.unwrap_or(Loc::Implicit),
                                                ),
                                            ),
                                            analysis_ty: ArrayAccess::MinSize,
                                        },
                                        e => {
                                            panic!("Attempt to index into an array with a {:?}", e)
                                        }
                                    }
                                }
                                VarType::BuiltIn(_bn, maybe_range) => {
                                    // its a variable index, the analysis should be a Gt the variable
                                    // the range will tell us more about the actual bounds
                                    if let Some(_range) = maybe_range {
                                        ArrayAccessAnalysis {
                                            arr_def: ContextVarNode::from(*array),
                                            arr_loc: LocSpan(
                                                ContextVarNode::from(*array).loc(self),
                                            ),
                                            def_loc: LocSpan(def.loc.expect("No loc for access")),
                                            access_loc: LocSpan(
                                                cvar.loc.expect("No loc for access"),
                                            ),
                                            analysis: Analysis::Relative(
                                                Relative::Gt,
                                                RangeElem::Dynamic(
                                                    cvar_idx,
                                                    cvar.loc.unwrap_or(Loc::Implicit),
                                                ),
                                            ),
                                            analysis_ty: ArrayAccess::MinSize,
                                        }
                                    } else {
                                        ArrayAccessAnalysis {
                                            arr_def: ContextVarNode::from(*array),
                                            arr_loc: LocSpan(
                                                ContextVarNode::from(*array).loc(self),
                                            ),
                                            def_loc: LocSpan(def.loc.expect("No loc for access")),
                                            access_loc: LocSpan(
                                                cvar.loc.expect("No loc for access"),
                                            ),
                                            analysis: Analysis::Relative(
                                                Relative::Gt,
                                                RangeElem::Dynamic(
                                                    *access,
                                                    cvar.loc.unwrap_or(Loc::Implicit),
                                                ),
                                            ),
                                            analysis_ty: ArrayAccess::MinSize,
                                        }
                                    }
                                }
                                e => panic!("Attempt to index into an array with a {:?}", e),
                            }
                        })
                        .collect::<Vec<ArrayAccessAnalysis>>()
                })
                .collect();
        }

        analyses
    }

    fn max_size_to_prevent_access_revert(
        &self,
        ctx: ContextNode,
    ) -> BTreeMap<NodeIdx, Vec<Analysis>> {
        todo!()
    }
}

pub trait JumpAnalyzer: AnalyzerLike {}
