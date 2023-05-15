use crate::analyzers::{VarBoundAnalyzer, *};
use shared::{
    analyzer::*,
    context::ContextNode,
    nodes::{TypeNode, VarType},
    NodeIdx,
};

use ariadne::{Cache, Color, Config, Label, Report, ReportKind};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct AccessStorageWriteReport {
    pub msgs: Vec<String>,
}

impl AccessStorageWriteReport {
    pub fn new(msgs: Vec<String>) -> Self {
        Self { msgs }
    }
}

impl ReportDisplay for AccessStorageWriteReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Access Analysis", Color::Green)
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

impl<T> AccessStorageWriteQuery for T where T: VarBoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait AccessStorageWriteQuery: VarBoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn access_query(
        &self,
        _entry: NodeIdx,
        _file_mapping: &'_ BTreeMap<usize, String>,
        _report_config: ReportConfig,
        _contract_name: String,
        _storage_var_name: String,
    ) -> AccessStorageWriteReport {
        todo!()
    }

    fn recurse(&self, ctx: ContextNode, storage_var_name: String) -> Vec<String> {
        if let Some(cvar) = ctx.var_by_name(self, &storage_var_name) {
            match cvar.ty(self).unwrap() {
                VarType::User(TypeNode::Struct(s_node), _) => {
                    let fields = s_node
                        .fields(self)
                        .iter()
                        .map(|field| format!("{}.{}", storage_var_name, field.name(self).unwrap()))
                        .collect();
                    fields
                }
                _ => vec![storage_var_name],
            }
        } else {
            vec![storage_var_name]
        }
    }
}
