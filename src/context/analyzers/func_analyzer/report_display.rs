use crate::analyzers::func_analyzer::*;
use crate::analyzers::{LocStrSpan, ReportDisplay};
use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use shared::analyzer::GraphLike;
use std::collections::BTreeMap;

pub struct CLIFunctionVarsBoundAnalysis<'a> {
    pub file_mapping: &'a BTreeMap<usize, String>,
    pub func_var_bound_analysis: FunctionVarsBoundAnalysis,
}

impl<'a> CLIFunctionVarsBoundAnalysis<'a> {
    pub fn new(
        file_mapping: &'a BTreeMap<usize, String>,
        func_var_bound_analysis: FunctionVarsBoundAnalysis,
    ) -> Self {
        Self {
            file_mapping,
            func_var_bound_analysis,
        }
    }
}

impl<'a> ReportDisplay for CLIFunctionVarsBoundAnalysis<'a> {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &impl GraphLike) -> String {
        format!(
            "Bounds for function: {}",
            format!(
                "function {}",
                self.func_var_bound_analysis
                    .ctx
                    .associated_fn_name(analyzer)
                    .unwrap()
            )
            .fg(Color::Cyan)
        )
    }

    fn labels(&self, _analyzer: &impl GraphLike) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &impl GraphLike) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            self.func_var_bound_analysis.ctx_loc.source(),
            self.func_var_bound_analysis.ctx_loc.start(),
        )
        .with_message(self.msg(analyzer))
        .with_config(
            Config::default()
                .with_cross_gap(false)
                .with_underlines(true)
                .with_tab_width(4),
        );

        report.add_labels(self.labels(analyzer));
        if let Some(killed_span) = &self.func_var_bound_analysis.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message("Execution guaranteed to revert here!".fg(Color::Red))
                    .with_color(Color::Red),
            );
        }

        let mut reports = vec![report.finish()];

        // let mut called_fns = BTreeSet::new();
        // let mut added_fn_calls = BTreeSet::new();
        // let mut called_contracts = BTreeSet::new();
        // let mut called_external_fns = BTreeSet::new();

        reports.extend(
            self.func_var_bound_analysis
                .reports_for_forks(self.file_mapping, analyzer),
        );

        reports
    }

    fn print_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        for report in reports.iter() {
            report.print(&mut src).unwrap();
        }
    }

    fn eprint_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        reports.iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}
