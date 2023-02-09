use crate::analyzers::*;
use ariadne::Cache;
use ariadne::{Color, Label, Report, ReportKind};
use shared::analyzer::*;
use shared::context::ContextNode;
use shared::nodes::ContractNode;

use shared::range::elem::RangeElem;
use shared::range::range_string::ToRangeString;
use shared::range::Range;

use shared::NodeIdx;
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct AccessStorageWriteReport {
    pub target: String,
    pub write_ctxs: Vec<ContextNode>,
}

impl ReportDisplay for AccessStorageWriteReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Storage Write Query", Color::Green)
    }
    fn msg(&self, _analyzer: &(impl AnalyzerLike + Search)) -> String {
        "".to_string()
    }

    fn labels(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
        vec![]
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

impl<T> AccessStorageWriteQuery for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait AccessStorageWriteQuery: BoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn access_query(
        &self,
        entry: NodeIdx,
        file_mapping: &'_ BTreeMap<usize, String>,
        report_config: ReportConfig,
        contract_name: String,
        storage_var_name: String,
    ) {
        // perform analysis on the contract for the storage var
        // collect bound changes of the var
        let contract = self
            .search_children(entry, &crate::Edge::Contract)
            .into_iter()
            .filter(|contract| ContractNode::from(*contract).name(self) == contract_name)
            .take(1)
            .next()
            .expect("No contract with provided name");

        let con_node = ContractNode::from(contract);
        let mut write_ctxs = vec![];
        for func in con_node.funcs(self) {
            let ctx = func.body_ctx(self);
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
                .filter(|analysis| !analysis.bound_changes.is_empty())
            {
                // filter spurious bound changes
                if analysis.bound_changes.len() < 2 {
                    if let Some(init) = analysis.var_def.1 {
                        if init.range_min().eval(self)
                            == analysis.bound_changes[0].1.range_min().eval(self)
                            && init.range_max().eval(self)
                                == analysis.bound_changes[0].1.range_max().eval(self)
                        {
                            continue;
                        }
                    }
                }

                write_ctxs.push(analysis.ctx);
            }
        }

        if write_ctxs.is_empty() {
            println!("No write access for storage var \"{}\"", storage_var_name);
        } else {
            write_ctxs.iter().for_each(|ctx| {
                let bounds_string = ctx
                    .ctx_deps(self)
                    .iter()
                    .filter_map(|(_name, cvar)| {
                        let min = if report_config.eval_bounds {
                            cvar.range(self)?
                                .range_min()
                                .eval(self)
                                .to_range_string(self)
                                .s
                        } else if report_config.simplify_bounds {
                            cvar.range(self)?
                                .range_min()
                                .simplify(self)
                                .to_range_string(self)
                                .s
                        } else {
                            cvar.range(self)?.range_min().to_range_string(self).s
                        };

                        let max = if report_config.eval_bounds {
                            cvar.range(self)?
                                .range_max()
                                .eval(self)
                                .to_range_string(self)
                                .s
                        } else if report_config.simplify_bounds {
                            cvar.range(self)?
                                .range_max()
                                .simplify(self)
                                .to_range_string(self)
                                .s
                        } else {
                            cvar.range(self)?.range_max().to_range_string(self).s
                        };
                        if min == max {
                            Some(format!("\"{}\" == {}", cvar.display_name(self), min,))
                        } else {
                            Some(format!(
                                "\"{}\" ∈ [ {}, {} ]",
                                cvar.display_name(self),
                                min,
                                max,
                            ))
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ∧ ");

                if bounds_string.is_empty() {
                    println!(
                        "Unrestricted write access of storage var \"{}\" via: function \"{}\"",
                        storage_var_name,
                        ctx.associated_fn_name(self)
                    );
                } else {
                    println!(
                        "Write access of storage var \"{}\" via: function \"{}\" if {}",
                        storage_var_name,
                        ctx.associated_fn_name(self),
                        bounds_string
                    );
                }
            });
        }
    }
}
