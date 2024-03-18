use crate::{
    bounds::range_parts, LocStrSpan, ReportConfig, ReportDisplay, ReportKind, VarBoundAnalysis,
    VarBoundAnalyzer,
};

use graph::{
    nodes::{ContextNode, KilledKind},
    AnalyzerBackend, GraphBackend,
};
use shared::Search;

use ariadne::{Color, Config, Fmt, Label, Report, Span};
use solang_parser::pt::CodeLocation;
use std::collections::{BTreeMap, BTreeSet};

mod report_display;
pub use report_display::*;

#[derive(Debug, Clone)]
pub struct FunctionVarsBoundAnalysis {
    /// Entry context location string span
    pub ctx_loc: LocStrSpan,
    /// Entry context
    pub ctx: ContextNode,
    /// If the context was killed (i.e. a `return` or `revert` of some kind), the location string span
    pub ctx_killed: Option<(LocStrSpan, KilledKind)>,
    /// The report configuration
    pub report_config: ReportConfig,
    /// Mapping of context node (i.e. for the lineage of the entry context) to a vector of bound analyses
    pub vars_by_ctx: BTreeMap<ContextNode, Vec<VarBoundAnalysis>>,
}

impl<'a> FunctionVarsBoundAnalysis {
    pub fn as_cli_compat(
        self,
        file_mapping: &'a BTreeMap<usize, String>,
    ) -> CLIFunctionVarsBoundAnalysis<'a> {
        CLIFunctionVarsBoundAnalysis::new(file_mapping, self)
    }

    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }

    pub fn reports_for_forks(
        &self,
        file_mapping: &'a BTreeMap<usize, String>,
        analyzer: &impl GraphBackend,
    ) -> Vec<Report<LocStrSpan>> {
        let mut handled_ctx_switches = BTreeSet::default();
        let reports = self
            .vars_by_ctx
            .iter()
            .map(|(ctx, analyses)| {
                // sort by display name instead of normal name
                let deps = ctx.ctx_deps(analyzer).unwrap();
                let deps = deps
                    .iter()
                    .map(|var| (var.as_controllable_name(analyzer).unwrap(), var))
                    .collect::<BTreeMap<_, _>>();
                // create the bound strings
                // let atoms = ctx.dep_atoms(analyzer).unwrap();
                // println!("had {} atoms", atoms.len());
                // let mut handled_atom = vec![];
                // let mut bounds_string: Vec<String> = vec![];
                // atoms.iter().enumerate().for_each(|(i, atom)| {
                //     let atom_str = atom.to_range_string(true, analyzer).s;
                //     if !handled_atom.contains(&atom_str) {
                //         handled_atom.push(atom_str.clone());
                //         bounds_string.push(format!("{}. {}", i + 1, atom_str))
                //     }
                // });
                // let bounds_string = bounds_string.into_iter().collect::<Vec<_>>().join("\n");

                let bounds_string = deps
                    .iter()
                    .enumerate()
                    .filter_map(|(i, (name, cvar))| {
                        let range = cvar.ref_range(analyzer).unwrap()?;

                        let (parts, _unsat) = range_parts(analyzer, &self.report_config, &range);
                        let ret = parts.into_iter().fold(
                            format!("{}. {name}", i + 1),
                            |mut acc, _part| {
                                acc = acc.to_string();
                                acc
                            },
                        );
                        Some(format!("{ret}\n"))
                    })
                    .collect::<Vec<_>>()
                    .join("");
                let mut report = Report::build(
                    self.report_kind(),
                    self.ctx_loc.source(),
                    self.ctx_loc.start(),
                )
                .with_message(format!(
                    "Bounds for subcontext: {}{}{}, killed: {:?}",
                    ctx.path(analyzer).fg(Color::Cyan),
                    if bounds_string.is_empty() {
                        ""
                    } else {
                        " where:\n"
                    },
                    bounds_string.fg(Color::Yellow),
                    ctx.underlying(analyzer).unwrap().killed
                ))
                .with_config(
                    Config::default()
                        .with_cross_gap(false)
                        .with_underlines(true)
                        .with_tab_width(4)
                        .with_multiline_arrows(false),
                );

                let mut self_handled = false;
                let mut added_bodies = vec![];
                let mut labels: Vec<_> = analyses
                    .iter()
                    .flat_map(|analysis| {
                        let mut labels = analysis.labels(analyzer);
                        labels.extend(
                            analysis
                                .spanned_ctx_info
                                .clone()
                                .into_iter()
                                .filter_map(|ctx_switch| {
                                    let mut is_self = false;
                                    if ctx_switch.ctx == *ctx
                                        || ctx_switch.ctx.underlying(analyzer).unwrap().depth == 0
                                    {
                                        self_handled = true;
                                        is_self = true;
                                    }

                                    if let Some(body) = ctx_switch.func_body_span {
                                        if added_bodies.contains(&body) {
                                            return None;
                                        }
                                        added_bodies.push(body.clone());
                                        if is_self {
                                            Some(
                                                Label::new(body)
                                                    .with_message("Entry function call")
                                                    .with_color(Color::White)
                                                    .with_priority(-2)
                                                    .with_order(-2),
                                            )
                                        } else {
                                            Some(
                                                Label::new(body)
                                                    .with_message("Function call")
                                                    .with_color(Color::Fixed(140))
                                                    .with_priority(-2)
                                                    .with_order(-2),
                                            )
                                        }
                                    } else {
                                        if added_bodies.contains(&ctx_switch.func_span) {
                                            return None;
                                        }
                                        added_bodies.push(ctx_switch.func_span.clone());
                                        if is_self {
                                            Some(
                                                Label::new(ctx_switch.func_span)
                                                    .with_message("Entry function call")
                                                    .with_color(Color::White)
                                                    .with_priority(-2)
                                                    .with_order(-2),
                                            )
                                        } else {
                                            Some(
                                                Label::new(ctx_switch.func_span)
                                                    .with_message("Function call")
                                                    .with_color(Color::Fixed(140))
                                                    .with_priority(-2)
                                                    .with_order(-2),
                                            )
                                        }
                                    }
                                })
                                .collect::<Vec<_>>(),
                        );

                        analysis.spanned_ctx_info.iter().for_each(|ctx_switch| {
                            if !handled_ctx_switches.contains(ctx_switch) {
                                handled_ctx_switches.insert(ctx_switch);
                                if ctx_switch.ctx != *ctx {
                                    labels.extend(
                                        ctx_switch
                                            .ctx
                                            .return_nodes(analyzer)
                                            .unwrap()
                                            .into_iter()
                                            .filter_map(|(loc, var)| {
                                                let range = var.ref_range(analyzer).unwrap()?;
                                                let (parts, _unsat) = range_parts(
                                                    analyzer,
                                                    &self.report_config,
                                                    &range,
                                                );
                                                Some(
                                                    Label::new(LocStrSpan::new(file_mapping, loc))
                                                        .with_message(
                                                            format!(
                                                                "returns: \"{}\"{}",
                                                                var.display_name(analyzer).unwrap(),
                                                                parts
                                                                    .into_iter()
                                                                    .map(|i| i.to_cli_string())
                                                                    .collect::<Vec<_>>()
                                                                    .join(", ")
                                                            )
                                                            .fg(Color::Yellow),
                                                        )
                                                        .with_color(Color::Yellow)
                                                        .with_order(50),
                                                )
                                            })
                                            .collect::<Vec<_>>(),
                                    );
                                }
                                if ctx_switch.ctx == *ctx {
                                    if let Some((killed_loc, kind)) = &ctx_switch.killed_loc {
                                        labels.push(
                                            Label::new(killed_loc.clone())
                                                .with_message(kind.analysis_str())
                                                .with_color(Color::Red)
                                                .with_priority(10),
                                        );
                                    }
                                    self_handled = true;
                                }
                            }
                        });
                        labels
                    })
                    .collect();

                if let Some((killed_span, kind)) = &self.ctx_killed {
                    if !self_handled {
                        labels.push(
                            Label::new(killed_span.clone())
                                .with_message(kind.analysis_str().fg(Color::Red))
                                .with_color(Color::Red),
                        );
                    }
                }

                labels.extend(
                    ctx.return_nodes(analyzer)
                        .unwrap()
                        .into_iter()
                        .filter_map(|(loc, var)| {
                            let range = var.ref_range(analyzer).unwrap()?;
                            let (parts, _unsat) =
                                range_parts(analyzer, &self.report_config, &range);
                            Some(
                                Label::new(LocStrSpan::new(file_mapping, loc))
                                    .with_message(
                                        format!(
                                            "returns: \"{}\"{}",
                                            var.display_name(analyzer).unwrap(),
                                            parts
                                                .into_iter()
                                                .map(|i| i.to_cli_string())
                                                .collect::<Vec<_>>()
                                                .join(", ")
                                        )
                                        .fg(Color::Yellow),
                                    )
                                    .with_color(Color::Yellow)
                                    .with_order(50),
                            )
                        })
                        .collect::<Vec<_>>(),
                );
                if !self_handled {
                    if let Some(body) = ctx
                        .associated_fn(analyzer)
                        .unwrap()
                        .underlying(analyzer)
                        .unwrap()
                        .body
                        .as_ref()
                    {
                        report.add_label(
                            Label::new(LocStrSpan::new(file_mapping, body.loc()))
                                .with_message("Entry function call")
                                .with_priority(-2)
                                .with_order(-2),
                        );
                    }
                }

                report.add_labels(labels);
                report.finish()
            })
            .collect::<Vec<Report<LocStrSpan>>>();
        reports
    }
}

impl<T> FunctionVarsBoundAnalyzer for T where T: VarBoundAnalyzer + Search + AnalyzerBackend + Sized {}
pub trait FunctionVarsBoundAnalyzer: VarBoundAnalyzer + Search + AnalyzerBackend + Sized {
    fn bounds_for_lineage<'a>(
        &'a self,
        file_mapping: &'a BTreeMap<usize, String>,
        ctx: ContextNode,
        edges: Vec<ContextNode>,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        let lineage_analyses = edges
            .iter()
            .filter_map(|fork| {
                if !report_config.show_unreachables
                    && matches!(
                        fork.underlying(self).unwrap().killed,
                        Some((_, KilledKind::Unreachable))
                    )
                {
                    return None;
                }
                if !report_config.show_nonreverts && fork.underlying(self).unwrap().killed.is_none()
                {
                    return None;
                }
                if !report_config.show_reverts
                    && matches!(
                        fork.underlying(self).unwrap().killed,
                        Some((_, KilledKind::Revert))
                    )
                {
                    return None;
                }
                let mut parents = fork.parent_list(self).unwrap();
                parents.reverse();
                parents.push(*fork);
                let mut vars = ctx.vars(self).values().collect::<Vec<_>>();
                vars.extend(
                    parents
                        .iter()
                        .flat_map(|parent| parent.vars(self).values().collect::<Vec<_>>())
                        .collect::<Vec<_>>(),
                );
                vars.sort_by_key(|a| a.name(self));
                vars.dedup_by(|a, b| a.name(self) == b.name(self));
                Some((
                    *fork,
                    vars.iter()
                        .filter_map(|var| {
                            let is_ret = var.is_return_node_in_any(&parents, self);
                            if is_ret
                                | report_config.show_tmps
                                | (report_config.show_consts && var.is_const(self).unwrap())
                                | (report_config.show_symbolics && var.is_symbolic(self).unwrap())
                            {
                                Some(self.bounds_for_var_in_family_tree(
                                    file_mapping,
                                    parents.clone(),
                                    var.name(self).unwrap(),
                                    report_config,
                                ))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<VarBoundAnalysis>>(),
                ))
            })
            .collect::<BTreeMap<ContextNode, Vec<VarBoundAnalysis>>>();

        FunctionVarsBoundAnalysis {
            ctx_loc: LocStrSpan::new(file_mapping, ctx.underlying(self).unwrap().loc),
            ctx,
            ctx_killed: ctx
                .killed_loc(self)
                .unwrap()
                .map(|(loc, kind)| (LocStrSpan::new(file_mapping, loc), kind)),
            vars_by_ctx: lineage_analyses,
            report_config,
        }
    }

    fn bounds_for_all<'a>(
        &'a self,
        file_mapping: &'a BTreeMap<usize, String>,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        let mut edges = ctx.all_edges(self).unwrap();
        if edges.is_empty() {
            edges.push(ctx);
        }
        self.bounds_for_lineage(file_mapping, ctx, edges, report_config)
    }
}
