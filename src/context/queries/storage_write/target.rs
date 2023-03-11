use crate::analyzers::{
    bounds::{BoundAnalysis, BoundAnalyzer},
    *,
};
use shared::{
    analyzer::*,
    nodes::{ContractNode, FunctionNode},
    range::{range_string::ToRangeString, Range, RangeEval, SolcRange},
    NodeIdx,
};

use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct StorageRangeReport {
    pub target: SolcRange,
    pub write_loc: Option<LocStrSpan>,
    pub analysis: BoundAnalysis,
}

impl ReportDisplay for StorageRangeReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Storage Write Query", Color::Green)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        let bounds_string = self
            .analysis
            .ctx
            .ctx_deps(analyzer)
            .iter()
            .filter_map(|(_name, cvar)| {
                let min = if self.analysis.report_config.eval_bounds {
                    cvar.range(analyzer)?
                        .evaled_range_min(analyzer)
                        .to_range_string(false, analyzer)
                        .s
                } else if self.analysis.report_config.simplify_bounds {
                    cvar.range(analyzer)?
                        .simplified_range_min(analyzer)
                        .to_range_string(false, analyzer)
                        .s
                } else {
                    cvar.range(analyzer)?
                        .range_min()
                        .to_range_string(false, analyzer)
                        .s
                };

                let max = if self.analysis.report_config.eval_bounds {
                    cvar.range(analyzer)?
                        .evaled_range_max(analyzer)
                        .to_range_string(true, analyzer)
                        .s
                } else if self.analysis.report_config.simplify_bounds {
                    cvar.range(analyzer)?
                        .simplified_range_max(analyzer)
                        .to_range_string(true, analyzer)
                        .s
                } else {
                    cvar.range(analyzer)?
                        .range_max()
                        .to_range_string(true, analyzer)
                        .s
                };

                Some(format!(
                    "\"{}\" ∈ {{{}, {}}}",
                    cvar.display_name(analyzer),
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
                .evaled_range_min(analyzer) .to_range_string(false, analyzer)
                .s,
            self.target
                .evaled_range_max(analyzer) .to_range_string(true, analyzer)
                .s,
            if bounds_string.is_empty() {
                ""
            } else {
                ", where "
            },
            bounds_string.fg(Color::Yellow)
        )
    }

    fn labels(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
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

        let mut reports = vec![report.finish()];

        if self.analysis.report_config.show_subctxs {
            reports.extend(
                self.analysis
                    .sub_ctxs
                    .iter()
                    .flat_map(|analysis| analysis.reports(analyzer))
                    .collect::<Vec<_>>(),
            );
        }

        reports
    }

    fn print_reports(&self, src: &mut impl Cache<String>, analyzer: &(impl AnalyzerLike + Search)) {
        let reports = &self.reports(analyzer);
        for report in reports.iter() {
            report.print(&mut *src).unwrap();
        }
    }

    fn eprint_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &(impl AnalyzerLike + Search),
    ) {
        let reports = &self.reports(analyzer);
        reports.iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}

impl<T> StorageRangeQuery for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait StorageRangeQuery: BoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn func_query(
        &self,
        entry: NodeIdx,
        file_mapping: &'_ BTreeMap<usize, String>,
        report_config: ReportConfig,
        contract_name: String,
        func_name: String,
        storage_var_name: String,
        target: SolcRange,
    ) -> Option<StorageRangeReport> {
        // perform analysis on the func for the storage var
        // collect bound changes of the var
        // check if any of the bound changes' mins are less than or equal
        // the target and if the maxs are greater than or equal the target
        // report back dependencies
        let contract = self
            .search_children(entry, &crate::Edge::Contract)
            .into_iter()
            .filter(|contract| ContractNode::from(*contract).name(self) == contract_name)
            .take(1)
            .next()
            .expect("No contract with provided name");
        let func = self
            .search_children(contract, &crate::Edge::Func)
            .into_iter()
            .filter(|func| FunctionNode::from(*func).name(self) == func_name)
            .take(1)
            .next()
            .expect("No function in contract with provided name");
        let ctx = FunctionNode::from(func).body_ctx(self);

        let terminals = ctx.terminal_child_list(self);
        for analysis in terminals
            .iter()
            .map(|child| {
                let mut parents = child.parent_list(self);
                parents.reverse();
                parents.push(*child);
                self.bounds_for_var_in_family_tree(
                    file_mapping,
                    parents.clone(),
                    storage_var_name.clone(),
                    report_config,
                )
            })
            .filter(|analysis| terminals.contains(&analysis.ctx))
            .filter(|analysis| !analysis.ctx.is_killed(self))
        {
            if let Some(last) = analysis.bound_changes.iter().last() {
                if last.1.contains(&target, self) {
                    return Some(StorageRangeReport {
                        target,
                        write_loc: Some(last.0.clone()),
                        analysis,
                    });
                }
            }
        }
        None
    }
}
