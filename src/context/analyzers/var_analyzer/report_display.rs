use crate::analyzers::{LocStrSpan, ReportDisplay};
use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use shared::analyzer::AnalyzerLike;
use shared::analyzer::GraphLike;

use crate::analyzers::var_analyzer::*;

impl ReportDisplay for VarBoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &impl GraphLike) -> String {
        format!(
            "Bounds for {} in {}:",
            self.var_display_name,
            self.ctx.underlying(analyzer).unwrap().path
        )
    }
    fn labels(&self, analyzer: &impl GraphLike) -> Vec<Label<LocStrSpan>> {
        let mut labels = if self.report_config.show_initial_bounds {
            if let Some(init_item) = self.init_item(analyzer) {
                vec![init_item.into()]
            } else {
                vec![]
            }
        } else {
            vec![]
        };

        labels.extend(
            self.bound_changes
                .iter()
                .enumerate()
                .map(|(i, bound_change)| {
                    let (parts, unsat) =
                        range_parts(analyzer, &self.report_config, &bound_change.1);
                    AnalysisItem {
                        init: false,
                        name: self.var_display_name.clone(),
                        loc: bound_change.0.clone(),
                        order: i as i32,
                        storage: self.storage.clone(),
                        ctx: self.ctx,
                        ctx_conditionals: self.conditionals(analyzer),
                        parts,
                        unsat,
                    }
                    .into()
                })
                .collect::<Vec<_>>(),
        );

        labels
    }

    fn reports(&self, analyzer: &impl GraphLike) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            self.var_def.0.source(),
            self.var_def.0.start(),
        )
        .with_message(self.msg(analyzer))
        .with_config(
            Config::default()
                .with_cross_gap(false)
                .with_underlines(true)
                .with_tab_width(4),
        );

        report.add_labels(self.labels(analyzer));

        if let Some(killed_span) = &self.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message("Execution guaranteed to revert here!".fg(Color::Red))
                    .with_color(Color::Red),
            );
        }

        let reports = vec![report.finish()];

        // if self.report_config.show_subctxs {
        //     reports.extend(
        //         self.sub_ctxs
        //             .iter()
        //             .flat_map(|analysis| analysis.reports(analyzer))
        //             .collect::<Vec<_>>(),
        //     );
        // }

        reports
    }

    fn print_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print(&mut src).unwrap();
        });
    }

    fn eprint_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}
