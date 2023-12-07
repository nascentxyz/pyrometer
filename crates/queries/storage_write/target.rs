use crate::analyzers::{VarBoundAnalyzer, *};
use shared::{
    analyzer::*,
    range::{range_string::ToRangeString, Range, SolcRange},
    NodeIdx,
};

use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct StorageRangeReport {
    pub target: SolcRange,
    pub write_loc: Option<LocStrSpan>,
    pub analysis: VarBoundAnalysis,
}

impl ReportDisplay for StorageRangeReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Storage Write Query", Color::Green)
    }
    fn msg(&self, analyzer: &impl GraphLike) -> String {
        let bounds_string = self
            .analysis
            .ctx
            .ctx_deps(analyzer)
            .unwrap()
            .iter()
            .filter_map(|(_name, cvar)| {
                let min = if self.analysis.report_config.eval_bounds {
                    cvar.range(analyzer)
                        .unwrap()?
                        .evaled_range_min(analyzer)
                        .unwrap()
                        .to_range_string(false, analyzer)
                        .s
                } else if self.analysis.report_config.simplify_bounds {
                    cvar.range(analyzer)
                        .unwrap()?
                        .simplified_range_min(analyzer)
                        .unwrap()
                        .to_range_string(false, analyzer)
                        .s
                } else {
                    cvar.range(analyzer)
                        .unwrap()?
                        .range_min()
                        .to_range_string(false, analyzer)
                        .s
                };

                let max = if self.analysis.report_config.eval_bounds {
                    cvar.range(analyzer)
                        .unwrap()?
                        .evaled_range_max(analyzer)
                        .unwrap()
                        .to_range_string(true, analyzer)
                        .s
                } else if self.analysis.report_config.simplify_bounds {
                    cvar.range(analyzer)
                        .unwrap()?
                        .simplified_range_max(analyzer)
                        .unwrap()
                        .to_range_string(true, analyzer)
                        .s
                } else {
                    cvar.range(analyzer)
                        .unwrap()?
                        .range_max()
                        .to_range_string(true, analyzer)
                        .s
                };

                Some(format!(
                    "\"{}\" ∈ {{{}, {}}}",
                    cvar.display_name(analyzer).unwrap(),
                    min,
                    max,
                ))
            })
            .collect::<Vec<_>>()
            .join(" ∧ ");
        format!(
            "Found storage write that could lead to target value in ctx {}: \"{}\" ∈ {{{}, {}}}{}{} ",
            self.analysis.ctx.path(analyzer),
            self.analysis.var_name,
            self.target
                .evaled_range_min(analyzer).unwrap() .to_range_string(false, analyzer)
                .s,
            self.target
                .evaled_range_max(analyzer).unwrap() .to_range_string(true, analyzer)
                .s,
            if bounds_string.is_empty() {
                ""
            } else {
                ", where "
            },
            bounds_string.fg(Color::Yellow)
        )
    }

    fn labels(&self, _analyzer: &impl GraphLike) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &impl GraphLike) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.analysis.report_kind(),
            self.analysis.var_def.0.source(),
            self.analysis.var_def.0.start(),
        )
        .with_message(self.msg(analyzer))
        .with_config(
            Config::default()
                .with_cross_gap(false)
                .with_underlines(true)
                .with_tab_width(4),
        );

        report.add_labels(self.analysis.labels(analyzer));

        let reports = vec![report.finish()];
        reports
    }

    fn print_reports(&self, src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        for report in reports.iter() {
            report.print(&mut *src).unwrap();
        }
    }

    fn eprint_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        reports.iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}

impl<T> StorageRangeQuery for T where T: VarBoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait StorageRangeQuery: VarBoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn func_query(
        &mut self,
        _entry: NodeIdx,
        _file_mapping: &'_ BTreeMap<usize, String>,
        _report_config: ReportConfig,
        _contract_name: String,
        _func_name: String,
        _storage_var_name: String,
        _target: SolcRange,
    ) -> Option<StorageRangeReport> {
        todo!()
    }
}
