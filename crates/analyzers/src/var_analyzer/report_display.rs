use crate::{
    bounds::{range_parts, AnalysisItem},
    LocStrSpan, ReportDisplay, ReportKind, VarBoundAnalysis,
};

use graph::GraphBackend;

use ariadne::{Cache, Color, Config, Fmt, Label, Report, Span};

impl ReportDisplay for VarBoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &impl GraphBackend) -> String {
        format!(
            "Bounds for {} in {}:",
            self.var_display_name,
            self.ctx.underlying(analyzer).unwrap().path
        )
    }
    fn labels(&self, analyzer: &impl GraphBackend) -> Vec<Label<LocStrSpan>> {
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
                .map(|(_i, bound_change)| {
                    let (parts, unsat) =
                        range_parts(analyzer, &self.report_config, &bound_change.1);
                    AnalysisItem {
                        init: false,
                        name: self.var_display_name.clone(),
                        loc: bound_change.0.clone(),
                        order: (bound_change.0.end() - bound_change.0.start()) as i32,
                        storage: self.storage,
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

    fn reports(&self, analyzer: &impl GraphBackend) -> Vec<Report<LocStrSpan>> {
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
                .with_index_type(ariadne::IndexType::Byte)
                .with_tab_width(4),
        );

        report.add_labels(self.labels(analyzer));

        if let Some((killed_span, kind)) = &self.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message(kind.analysis_str().fg(Color::Red))
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

    fn print_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphBackend) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print(&mut src).unwrap();
        });
    }

    fn eprint_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphBackend) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}
