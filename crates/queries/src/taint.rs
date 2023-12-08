use crate::analyzers::{VarBoundAnalyzer, *};
use shared::context::CallFork;

use shared::{analyzer::*, NodeIdx};

use ariadne::{Cache, Color, Config, Label, Report, ReportKind};

#[derive(Debug, Clone)]
pub struct TaintReport {
    pub msgs: Vec<String>,
}

impl TaintReport {
    pub fn new(msgs: Vec<String>) -> Self {
        Self { msgs }
    }
}

impl ReportDisplay for TaintReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Taint Analysis", Color::Green)
    }
    fn msg(&self, _analyzer: &impl GraphLike) -> String {
        self.msgs.join(";\n")
    }

    fn labels(&self, _analyzer: &impl GraphLike) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &impl GraphLike) -> Vec<Report<LocStrSpan>> {
        let report = Report::build(self.report_kind(), "".to_string(), 0)
            .with_message(self.msg(analyzer))
            .with_config(
                Config::default()
                    .with_cross_gap(false)
                    .with_underlines(true)
                    .with_tab_width(4),
            );
        vec![report.finish()]
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

impl<T> TaintQuery for T where T: VarBoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait TaintQuery: VarBoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn taint_query(&self, _entry: NodeIdx, _contract_name: String) {
        todo!()
    }

    fn recurse_children(&self, _child: CallFork) {
        todo!()
    }
}
