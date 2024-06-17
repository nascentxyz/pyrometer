use crate::{FunctionVarsBoundAnalysis, LocStrSpan, ReportDisplay, ReportKind};

use graph::{elem::Elem, nodes::Concrete, GraphBackend};

use shared::RangeArena;

use ariadne::{Cache, Color, Config, Fmt, Label, Report, Span};

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
    fn msg(&self, analyzer: &impl GraphBackend, _arena: &mut RangeArena<Elem<Concrete>>) -> String {
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

    fn labels(
        &self,
        _analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            self.func_var_bound_analysis.ctx_loc.source(),
            self.func_var_bound_analysis.ctx_loc.start(),
        )
        .with_message(self.msg(analyzer, arena))
        .with_config(
            Config::default()
                .with_cross_gap(false)
                .with_underlines(true)
                .with_tab_width(4),
        );

        report.add_labels(self.labels(analyzer, arena));
        if let Some((killed_span, kind)) = &self.func_var_bound_analysis.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message(kind.analysis_str().fg(Color::Red))
                    .with_color(Color::Red),
            );
        }

        let mut reports = vec![report.finish()];

        reports.extend(self.func_var_bound_analysis.reports_for_forks(
            self.file_mapping,
            analyzer,
            arena,
        ));

        reports
    }

    fn print_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        let reports = &self.reports(analyzer, arena);
        for report in reports.iter() {
            report.print(&mut src).unwrap();
        }
    }

    fn eprint_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) {
        let reports = &self.reports(analyzer, arena);
        reports.iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}
