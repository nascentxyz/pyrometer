use crate::range::ElemEval;
use crate::range::RangeSize;
use crate::range::ToRangeString;
use crate::{
    AnalyzerLike, BoundAnalysis, BoundAnalyzer, ContextEdge, ContextNode, ContextVarNode, Edge,
    LocSpan, ReportConfig, ReportDisplay, Search,
};
use ariadne::{Color, Fmt, Label, Report, ReportKind, Source, Span};
use solang_parser::pt::Loc;

#[derive(Debug, Clone)]
pub enum ArrayAccess {
    MinSize,
    MaxSize,
}

#[derive(Debug, Clone)]
pub struct ArrayAccessAnalysis {
    pub arr_def: ContextVarNode,
    pub arr_loc: LocSpan,
    pub access_loc: LocSpan,
    pub index_bounds: BoundAnalysis,
    pub dependent_bounds: Vec<BoundAnalysis>,
    pub analysis_ty: ArrayAccess,
    pub report_config: ReportConfig,
}

impl<T> ArrayAccessAnalyzer for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait ArrayAccessAnalyzer: BoundAnalyzer + Search + AnalyzerLike + Sized {
    fn min_size_to_prevent_access_revert(
        &self,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> Vec<ArrayAccessAnalysis> {
        // let mut analyses = Default::default();

        todo!();
        // if let Some(arrays) =
        //     self.nodes_with_children(ctx.into(), &Edge::Context(ContextEdge::IndexAccess))
        // {
        //     analyses = arrays
        //         .iter()
        //         .flat_map(|(array, accesses)| {
        //             accesses
        //                 .iter()
        //                 .map(|access| {
        //                     let cvar_idx = *self
        //                         .search_children(*access, &Edge::Context(ContextEdge::Index))
        //                         .iter()
        //                         .take(1)
        //                         .next()
        //                         .expect("IndexAccess without Index");
        //                     let cvar = ContextVarNode::from(cvar_idx);
        //                     let name = cvar.name(self);
        //                     let (index_bounds, dependent_bounds) =
        //                         self.bounds_for_var_node_and_dependents(name, cvar, report_config);
        //                     ArrayAccessAnalysis {
        //                         arr_def: ContextVarNode::from(*array),
        //                         arr_loc: LocSpan(ContextVarNode::from(*array).loc(self)),
        //                         access_loc: LocSpan(cvar.loc(self)),
        //                         index_bounds,
        //                         dependent_bounds,
        //                         analysis_ty: ArrayAccess::MinSize,
        //                         report_config,
        //                     }
        //                 })
        //                 .collect::<Vec<ArrayAccessAnalysis>>()
        //         })
        //         .collect();
        // }

        // analyses
    }

    // fn max_size_to_prevent_access_revert(
    //     &self,
    //     ctx: ContextNode,
    // ) -> BTreeMap<NodeIdx, Vec<Analysis>> {
    //     todo!()
    // }
}

impl ReportDisplay for ArrayAccessAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Advice
    }
    fn msg(&self, analyzer: &impl AnalyzerLike) -> String {
        let arr_name_len =
            format!("{}.length", self.arr_def.display_name(analyzer)).fg(Color::Green);
        let index_name = (&self.index_bounds.var_display_name).fg(Color::Green);
        let min = if let Some(last) = self.index_bounds.bound_changes.last() {
            if self.report_config.eval_bounds {
                last.1
                    .range_min()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            } else {
                last.1.range_min().to_range_string(analyzer).s
            }
        } else {
            if self.report_config.eval_bounds {
                self.index_bounds
                    .var_def
                    .1
                    .clone()
                    .expect("No initial bounds for variable")
                    .range_min()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            } else {
                self.index_bounds
                    .var_def
                    .1
                    .clone()
                    .expect("No initial bounds for variable")
                    .range_min()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            }
        };
        let max = if let Some(last) = self.index_bounds.bound_changes.last() {
            if self.report_config.eval_bounds {
                last.1
                    .range_max()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            } else {
                last.1.range_max().to_range_string(analyzer).s
            }
        } else {
            if self.report_config.eval_bounds {
                self.index_bounds
                    .var_def
                    .1
                    .clone()
                    .expect("No initial bounds for variable")
                    .range_max()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            } else {
                self.index_bounds
                    .var_def
                    .1
                    .clone()
                    .expect("No initial bounds for variable")
                    .range_max()
                    .eval(analyzer)
                    .to_range_string(analyzer)
                    .s
            }
        };
        match self.analysis_ty {
            ArrayAccess::MinSize => format!(
                "Minimum array length requirement: {} > {}, which {} is in the range {{{}, {}}}",
                arr_name_len, index_name, index_name, min, max
            ),
            ArrayAccess::MaxSize => "Maximum array length: length must be {}{}".to_string(),
        }
    }
    fn labels(&self, analyzer: &impl AnalyzerLike) -> Vec<Label<LocSpan>> {
        let mut labels = self.index_bounds.labels(analyzer);

        labels.extend(
            self.dependent_bounds
                .iter()
                .flat_map(|bound| bound.labels(analyzer))
                .collect::<Vec<_>>(),
        );

        labels.extend([
            Label::new(self.arr_loc)
                .with_message("Array accessed here")
                .with_color(Color::Green),
            Label::new(self.index_bounds.var_def.0)
                .with_message(format!(
                    "Length enforced by this variable: {}",
                    self.index_bounds.var_display_name
                ))
                .with_color(Color::Red),
        ]);

        if self.access_loc.0 != Loc::Implicit {
            labels.push(Label::new(self.access_loc).with_message("Index access defined here"));
        }

        labels
    }
    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            *self.arr_loc.source(),
            self.arr_loc.start(),
        )
        .with_message(self.msg(analyzer));

        for label in self.labels(analyzer).into_iter() {
            report = report.with_label(label);
        }

        vec![report.finish()]
    }
    fn print_reports(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let report = &self.reports(analyzer)[0];
        report.print((src.0, Source::from(src.1))).unwrap()
    }
}
