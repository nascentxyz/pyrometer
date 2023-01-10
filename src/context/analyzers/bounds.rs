use crate::{
    AnalyzerLike, ContextNode, ContextVarNode, LocSpan, Range, ReportConfig, ReportDisplay, Search,
};

use ariadne::{Color, Fmt, Label, Report, ReportKind, Source, Span};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct BoundAnalysis {
    pub var_name: String,
    pub var_display_name: String,
    pub var_def: (LocSpan, Option<Range>),
    pub bound_changes: Vec<(LocSpan, Range)>,
    pub report_config: ReportConfig,
}

impl ReportDisplay for BoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, _analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!("Bounds for {}:", self.var_display_name)
    }
    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>> {
        let mut labels = if let Some(init_range) = &self.var_def.1 {
            vec![Label::new(self.var_def.0)
                .with_message(format!(
                    "\"{}\" ∈ {{{}, {}}}",
                    self.var_display_name,
                    if self.report_config.eval_bounds {
                        init_range.min.eval(analyzer).to_range_string(analyzer).s
                    } else {
                        init_range.min.to_range_string(analyzer).s
                    },
                    if self.report_config.eval_bounds {
                        init_range.max.eval(analyzer).to_range_string(analyzer).s
                    } else {
                        init_range.max.to_range_string(analyzer).s
                    }
                ))
                .with_color(Color::Magenta)]
        } else {
            vec![]
        };

        labels.extend(
            self.bound_changes
                .iter()
                .map(|bound_change| {
                    let min = if self.report_config.eval_bounds {
                        bound_change
                            .1
                            .min
                            .eval(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else {
                        bound_change.1.min.to_range_string(analyzer).s
                    };

                    let max = if self.report_config.eval_bounds {
                        bound_change
                            .1
                            .max
                            .eval(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else {
                        bound_change.1.max.to_range_string(analyzer).s
                    };

                    Label::new(bound_change.0)
                        .with_message(format!(
                            "\"{}\" ∈ {{{}, {}}}",
                            self.var_display_name, min, max
                        ))
                        .with_color(Color::Cyan)
                })
                .collect::<Vec<_>>(),
        );

        labels
    }

    fn report(&self, analyzer: &(impl AnalyzerLike + Search)) -> Report<LocSpan> {
        let mut report = Report::build(
            self.report_kind(),
            *self.var_def.0.source(),
            self.var_def.0.start(),
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

impl<T> BoundAnalyzer for T where T: Search + AnalyzerLike + Sized {}
pub trait BoundAnalyzer: Search + AnalyzerLike + Sized {
    fn bounds_for_var(
        &self,
        ctx: ContextNode,
        var_name: String,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        if let Some(cvar) = ctx.latest_var_by_name(self, &var_name) {
            return self.bounds_for_var_node(var_name, cvar, report_config);
        }
        panic!("No variable in context with name: {}", var_name)
    }
    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node(
        &self,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        let mut curr = cvar.first_version(self);

        let mut ba = BoundAnalysis {
            var_name,
            var_display_name: cvar.display_name(self),
            var_def: (LocSpan(curr.loc(self)), curr.range(self)),
            bound_changes: vec![],
            report_config,
        };

        if let Some(mut curr_range) = curr.range(self) {
            while let Some(next) = curr.next_version(self) {
                if let Some(next_range) = next.range(self) {
                    if next_range != curr_range {
                        ba.bound_changes
                            .push((LocSpan(next.loc(self)), next_range.clone()));
                    }

                    curr_range = next_range;
                }

                if next == cvar {
                    break;
                } else {
                    curr = next;
                }
            }
        }

        return ba;
    }

    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node_and_dependents(
        &self,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
    ) -> (BoundAnalysis, Vec<BoundAnalysis>) {
        let bounds = self.bounds_for_var_node(var_name, cvar, report_config);
        let mut dependents = cvar.dependent_on(self, false);
        dependents.sort_by(|a, b| a.display_name(self).cmp(&b.display_name(self)));
        dependents.dedup_by(|a, b| a.display_name(self) == b.display_name(self));

        let dep_bounds = dependents
            .into_iter()
            .filter_map(
                |var| match (report_config.show_tmps, report_config.show_consts) {
                    (true, true) => {
                        let name = var.name(self);
                        Some(self.bounds_for_var_node(name, var, report_config))
                    }
                    (true, false) => {
                        if !var.is_tmp(self) {
                            let name = var.name(self);
                            Some(self.bounds_for_var_node(name, var, report_config))
                        } else {
                            None
                        }
                    }
                    (false, true) => {
                        if !var.is_const(self) {
                            let name = var.name(self);
                            Some(self.bounds_for_var_node(name, var, report_config))
                        } else {
                            None
                        }
                    }
                    (false, false) => {
                        if !var.is_tmp(self) && !var.is_const(self) {
                            let name = var.name(self);
                            Some(self.bounds_for_var_node(name, var, report_config))
                        } else {
                            None
                        }
                    }
                },
            )
            .collect();
        (bounds, dep_bounds)
    }
}

#[derive(Debug, Clone)]
pub struct FunctionVarsBoundAnalysis {
    pub ctx_loc: LocSpan,
    pub ctx: ContextNode,
    pub vars: BTreeMap<String, BoundAnalysis>,
}

impl ReportDisplay for FunctionVarsBoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!(
            "Bounds for context: {}",
            format!("function {}(..)", self.ctx.associated_fn_name(analyzer)).fg(Color::Cyan)
        )
    }

    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>> {
        self.vars
            .iter()
            .flat_map(|(_name, bound_analysis)| bound_analysis.labels(analyzer))
            .collect()
    }

    fn report(&self, analyzer: &(impl AnalyzerLike + Search)) -> Report<LocSpan> {
        let mut report = Report::build(
            self.report_kind(),
            *self.ctx_loc.source(),
            self.ctx_loc.start(),
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

impl<T> FunctionVarsBoundAnalyzer for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait FunctionVarsBoundAnalyzer: BoundAnalyzer + Search + AnalyzerLike + Sized {
    fn bounds_for_all(
        &self,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        let vars = ctx.vars(self);
        let analyses = vars
            .into_iter()
            .filter_map(
                |var| match (report_config.show_tmps, report_config.show_consts) {
                    (true, true) => {
                        let name = var.name(self);
                        Some((
                            name.clone(),
                            self.bounds_for_var_node(name, var, report_config),
                        ))
                    }
                    (true, false) => {
                        if !var.is_tmp(self) {
                            let name = var.name(self);
                            Some((
                                name.clone(),
                                self.bounds_for_var_node(name, var, report_config),
                            ))
                        } else {
                            None
                        }
                    }
                    (false, true) => {
                        if !var.is_const(self) {
                            let name = var.name(self);
                            Some((
                                name.clone(),
                                self.bounds_for_var_node(name, var, report_config),
                            ))
                        } else {
                            None
                        }
                    }
                    (false, false) => {
                        if !var.is_tmp(self) && !var.is_const(self) {
                            let name = var.name(self);
                            Some((
                                name.clone(),
                                self.bounds_for_var_node(name, var, report_config),
                            ))
                        } else {
                            None
                        }
                    }
                },
            )
            .collect();
        FunctionVarsBoundAnalysis {
            ctx_loc: LocSpan(ctx.underlying(self).loc),
            ctx,
            vars: analyses,
        }
    }
}
