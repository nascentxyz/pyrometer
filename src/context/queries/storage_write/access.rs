use crate::analyzers::{bounds::BoundAnalyzer, *};
use shared::{
    analyzer::*,
    context::ContextNode,
    nodes::{ContractNode, TypeNode, VarType},
    range::{range_string::ToRangeString, Range},
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
    fn msg(&self, _analyzer: &(impl AnalyzerLike + Search)) -> String {
        self.msgs.join(";\n")
    }

    fn labels(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
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
    ) -> AccessStorageWriteReport {
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
        for func in con_node
            .funcs(self)
            .iter()
            .filter(|func| func.is_public_or_ext(self))
        {
            let ctx = func.body_ctx(self);
            let terminals = ctx.terminal_child_list(self);
            let vars = self.recurse(ctx, storage_var_name.clone());
            for var in vars {
                for analysis in terminals
                    .iter()
                    .map(|child| {
                        let mut parents = child.parent_list(self);
                        parents.reverse();
                        parents.push(*child);
                        self.bounds_for_var_in_family_tree(
                            file_mapping,
                            parents.clone(),
                            var.clone(),
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
                            if init.evaled_range_min(self)
                                == analysis.bound_changes[0].1.evaled_range_min(self)
                                && init.evaled_range_max(self)
                                    == analysis.bound_changes[0].1.evaled_range_max(self)
                            {
                                continue;
                            }
                        }
                    }

                    write_ctxs.push(analysis.ctx);
                }
            }
        }

        if write_ctxs.is_empty() {
            AccessStorageWriteReport::new(vec![format!(
                "No write access for storage var \"{storage_var_name}\" after constructor"
            )])
        } else {
            let msgs = write_ctxs
                .iter()
                .map(|ctx| {
                    let bounds_string = ctx
                        .ctx_deps(self)
                        .iter()
                        .filter_map(|(_name, cvar)| {
                            let min = if report_config.eval_bounds {
                                cvar.range(self)?
                                    .evaled_range_min(self)
                                    .to_range_string(false, self)
                                    .s
                            } else if report_config.simplify_bounds {
                                cvar.range(self)?
                                    .simplified_range_min(self)
                                    .to_range_string(false, self)
                                    .s
                            } else {
                                cvar.range(self)?.range_min().to_range_string(false, self).s
                            };

                            let max = if report_config.eval_bounds {
                                cvar.range(self)?
                                    .evaled_range_max(self)
                                    .to_range_string(true, self)
                                    .s
                            } else if report_config.simplify_bounds {
                                cvar.range(self)?
                                    .simplified_range_max(self)
                                    .to_range_string(true, self)
                                    .s
                            } else {
                                cvar.range(self)?.range_max().to_range_string(true, self).s
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
                        format!(
                            "Unrestricted write access of storage var \"{}\" via: function \"{}\"",
                            storage_var_name,
                            ctx.associated_fn_name(self)
                        )
                    } else {
                        format!(
                            "Write access of storage var \"{}\" via: function \"{}\" if {}",
                            storage_var_name,
                            ctx.associated_fn_name(self),
                            bounds_string
                        )
                    }
                })
                .collect();
            AccessStorageWriteReport::new(msgs)
        }
    }

    fn recurse(&self, ctx: ContextNode, storage_var_name: String) -> Vec<String> {
        if let Some(cvar) = ctx.var_by_name(self, &storage_var_name) {
            match cvar.ty(self) {
                VarType::User(TypeNode::Struct(s_node)) => {
                    let fields = s_node
                        .fields(self)
                        .iter()
                        .map(|field| format!("{}.{}", storage_var_name, field.name(self)))
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
