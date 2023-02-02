use crate::LocStrSpan;
use crate::{ReportConfig, ReportDisplay};
use shared::range::elem::RangeElem;
use shared::range::range_string::*;
use shared::range::Range;
use shared::range::RangeEval;
use shared::range::SolcRange;
use shared::{
    analyzer::{AnalyzerLike, Search},
    context::*,
};

use ariadne::{Color, Config, Fmt, Label, Report, ReportKind, Source, Span};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct BoundAnalysis {
    pub ctx: ContextNode,
    pub var_name: String,
    pub var_display_name: String,
    pub var_def: (LocStrSpan, Option<SolcRange>),
    pub storage: bool,
    pub bound_changes: Vec<(LocStrSpan, SolcRange)>,
    pub report_config: ReportConfig,
    pub sub_ctxs: Vec<Self>,
}

impl Default for BoundAnalysis {
    fn default() -> Self {
        Self {
            ctx: ContextNode(0),
            var_name: Default::default(),
            var_display_name: Default::default(),
            var_def: Default::default(),
            bound_changes: Default::default(),
            report_config: Default::default(),
            sub_ctxs: Default::default(),
            storage: false,
        }
    }
}

impl BoundAnalysis {
    pub fn flatten_by_ctx(mut self) -> BTreeMap<ContextNode, BoundAnalysis> {
        let mut map =
            self.sub_ctxs
                .into_iter()
                .fold(BTreeMap::default(), |mut map, sub_analysis| {
                    let inner_map = sub_analysis.flatten_by_ctx();
                    inner_map.into_iter().for_each(|(path, analysis)| {
                        let entry: &mut BoundAnalysis = map.entry(path).or_default();
                        *entry = analysis;
                    });
                    map
                });

        self.sub_ctxs = vec![];
        let entry = map.entry(self.ctx.clone()).or_default();
        *entry = self;

        map
    }

    pub fn flatten_to_children(
        mut self,
        analyzer: &impl AnalyzerLike,
    ) -> BTreeMap<ContextNode, BoundAnalysis> {
        let children = self.ctx.forks(analyzer).len();
        let mut map =
            self.sub_ctxs
                .into_iter()
                .fold(BTreeMap::default(), |mut map, mut sub_analysis| {
                    if self.var_def.1.is_some() && !sub_analysis.var_def.1.is_some() {
                        sub_analysis.var_def = self.var_def.clone();
                    }
                    sub_analysis
                        .bound_changes
                        .splice(0..0, self.bound_changes.clone().drain(..));
                    let inner_map = sub_analysis.flatten_to_children(analyzer);
                    inner_map.into_iter().for_each(|(path, analysis)| {
                        let entry: &mut BoundAnalysis = map.entry(path).or_default();
                        *entry = analysis;
                    });
                    map
                });

        // if we had no sub_ctxs, we add self to the map
        if children == 0 {
            self.sub_ctxs = vec![];
            let entry = map.entry(self.ctx.clone()).or_default();
            *entry = self;
        }

        map
    }

    pub fn only_tails(mut self) -> BTreeMap<ContextNode, BoundAnalysis> {
        let children = self.sub_ctxs.len();
        let mut map =
            self.sub_ctxs
                .into_iter()
                .fold(BTreeMap::default(), |mut map, sub_analysis| {
                    let inner_map = sub_analysis.only_tails();
                    inner_map.into_iter().for_each(|(path, analysis)| {
                        let entry: &mut BoundAnalysis = map.entry(path).or_default();
                        *entry = analysis;
                    });
                    map
                });

        // if we had no sub_ctxs, we add self to the map
        if children == 0 {
            self.sub_ctxs = vec![];
            let entry = map.entry(self.ctx.clone()).or_default();
            *entry = self;
        }

        map
    }
}

impl ReportDisplay for BoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!(
            "Bounds for {} in {}:",
            self.var_display_name,
            self.ctx.underlying(analyzer).path
        )
    }
    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        let mut labels = if self.report_config.show_initial_bounds {
            if let Some(init_range) = &self.var_def.1 {
                vec![Label::new(self.var_def.0.clone())
                    .with_message(format!(
                        "{}\"{}\" ∈ {{{}, {}}}{}",
                        if self.storage { "storage var " } else { "" },
                        self.var_display_name,
                        if self.report_config.eval_bounds {
                            init_range
                                .range_min()
                                .eval(analyzer)
                                .to_range_string(analyzer)
                                .s
                        } else if self.report_config.simplify_bounds {
                            init_range
                                .range_min()
                                .simplify(analyzer)
                                .to_range_string(analyzer)
                                .s
                        } else {
                            init_range.range_min().to_range_string(analyzer).s
                        },
                        if self.report_config.eval_bounds {
                            init_range
                                .range_max()
                                .eval(analyzer)
                                .to_range_string(analyzer)
                                .s
                        } else if self.report_config.simplify_bounds {
                            init_range
                                .range_max()
                                .simplify(analyzer)
                                .to_range_string(analyzer)
                                .s
                        } else {
                            init_range.range_max().to_range_string(analyzer).s
                        },
                        if init_range.unsat(analyzer) {
                            " - unsatisfiable range, unreachable".fg(Color::Red)
                        } else {
                            "".fg(Color::Red)
                        }
                    ))
                    .with_color(Color::Magenta)]
            } else {
                vec![]
            }
        } else {
            vec![]
        };

        labels.extend(
            self.bound_changes
                .iter()
                .map(|bound_change| {
                    let min = if self.report_config.eval_bounds {
                        bound_change
                            .1
                            .range_min()
                            .eval(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else if self.report_config.simplify_bounds {
                        bound_change
                            .1
                            .range_min()
                            .simplify(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else {
                        bound_change.1.range_min().to_range_string(analyzer).s
                    };

                    let max = if self.report_config.eval_bounds {
                        bound_change
                            .1
                            .range_max()
                            .eval(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else if self.report_config.simplify_bounds {
                        bound_change
                            .1
                            .range_max()
                            .simplify(analyzer)
                            .to_range_string(analyzer)
                            .s
                    } else {
                        bound_change.1.range_max().to_range_string(analyzer).s
                    };

                    let label = Label::new(bound_change.0.clone()).with_message(format!(
                        "{}\"{}\" ∈ {{{}, {}}} {}",
                        if self.storage { "storage var " } else { "" },
                        self.var_display_name,
                        min,
                        max,
                        if bound_change.1.unsat(analyzer) {
                            "- unsatisfiable range, unreachable".fg(Color::Red)
                        } else {
                            "".fg(Color::Red)
                        }
                    ));

                    if !self.storage {
                        label.with_color(Color::Cyan)
                    } else {
                        label.with_color(Color::Green)
                    }
                })
                .collect::<Vec<_>>(),
        );

        labels
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
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

        let mut reports = vec![report.finish()];

        if self.report_config.show_subctxs {
            reports.extend(
                self.sub_ctxs
                    .iter()
                    .flat_map(|analysis| analysis.reports(analyzer))
                    .collect::<Vec<_>>(),
            );
        }

        reports
    }

    fn print_reports(&self, src: (String, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print((src.0.clone(), Source::from(src.1))).unwrap();
        });
    }

    fn eprint_reports(&self, src: (String, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.eprint((src.0.clone(), Source::from(src.1))).unwrap();
        });
    }
}

impl<T> BoundAnalyzer for T where T: Search + AnalyzerLike + Sized {}
pub trait BoundAnalyzer: Search + AnalyzerLike + Sized {
    fn bounds_for_var_in_family_tree<'a>(
        &self,
        file_mapping: &'a BTreeMap<usize, String>,
        ordered_ctxs: Vec<ContextNode>,
        var_name: String,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        let mut inherited = None;
        ordered_ctxs
            .into_iter()
            .filter_map(|ctx| Some((ctx, ctx.var_by_name(self, &var_name)?)))
            .for_each(|(ctx, cvar)| {
                let analysis = self.bounds_for_var_node(
                    inherited.clone(),
                    file_mapping,
                    var_name.clone(),
                    cvar,
                    report_config,
                    inherited.is_some(),
                );
                inherited = Some(analysis);
            });
        inherited.unwrap_or_default()
    }

    fn bounds_for_var<'a>(
        &self,
        inherited: Option<BoundAnalysis>,
        file_mapping: &'a BTreeMap<usize, String>,
        ctx: ContextNode,
        var_name: String,
        report_config: ReportConfig,
        is_subctx: bool,
    ) -> Vec<(bool, BoundAnalysis)> {
        println!(
            "ctx: {:?}, path: {}, var: {}",
            ctx,
            ctx.path(self),
            var_name
        );
        let mut analysis = None;
        if let Some(cvar) = ctx.var_by_name(self, &var_name) {
            analysis = Some(self.bounds_for_var_node(
                inherited.clone(),
                file_mapping,
                var_name.clone(),
                cvar,
                report_config,
                is_subctx,
            ));
        }

        let forks = ctx.forks(self);
        println!("forks: {:?}", forks);

        let mut sub_analyses = forks
            .iter()
            .flat_map(|fork_ctx| {
                if let Some(analysis) = &analysis {
                    self.bounds_for_var(
                        Some(analysis.clone()),
                        file_mapping,
                        *fork_ctx,
                        var_name.clone(),
                        report_config,
                        true,
                    )
                } else if let Some(inherited) = &inherited {
                    self.bounds_for_var(
                        Some(inherited.clone()),
                        file_mapping,
                        *fork_ctx,
                        var_name.clone(),
                        report_config,
                        true,
                    )
                } else {
                    self.bounds_for_var(
                        None,
                        file_mapping,
                        *fork_ctx,
                        var_name.clone(),
                        report_config,
                        true,
                    )
                }
            })
            .filter(|(keep, _)| *keep)
            .collect::<Vec<_>>();

        if let Some(analysis) = analysis {
            if forks.is_empty() || sub_analyses.is_empty() {
                sub_analyses.push((true, analysis));
            }
        }

        sub_analyses
    }

    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node<'a>(
        &self,
        inherited: Option<BoundAnalysis>,
        file_mapping: &'a BTreeMap<usize, String>,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
        is_subctx: bool,
    ) -> BoundAnalysis {
        let mut curr = cvar.first_version(self);

        let mut ba = if let Some(inherited) = inherited {
            let mut new_ba = inherited.clone();
            new_ba.ctx = cvar.ctx(self);
            new_ba
        } else {
            BoundAnalysis {
                ctx: cvar.ctx(self),
                var_name,
                var_display_name: cvar.display_name(self),
                var_def: (
                    LocStrSpan::new(&file_mapping, curr.loc(self)),
                    if !is_subctx { curr.range(self) } else { None },
                ),
                bound_changes: vec![],
                report_config,
                sub_ctxs: vec![],
                storage: curr.underlying(self).storage.is_some(),
            }
        };

        if let Some(mut curr_range) = curr.range(self) {
            while let Some(next) = curr.next_version(self) {
                if let Some(next_range) = next.range(self) {
                    if next_range != curr_range {
                        ba.bound_changes.push((
                            LocStrSpan::new(&file_mapping, next.loc(self)),
                            next_range.clone(),
                        ));
                    }

                    curr_range = next_range;
                }

                if next == cvar {
                    break;
                } else {
                    curr = next;
                }
            }
        }

        return ba;
    }
}

#[derive(Debug, Clone)]
pub struct FunctionVarsBoundAnalysis<'a> {
    pub file_mapping: &'a BTreeMap<usize, String>,
    pub ctx_loc: LocStrSpan,
    pub ctx: ContextNode,
    pub ctx_killed: Option<LocStrSpan>,
    pub report_config: ReportConfig,
    pub vars_by_ctx: BTreeMap<ContextNode, Vec<BoundAnalysis>>,
}

impl<'a> ReportDisplay for FunctionVarsBoundAnalysis<'a> {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!(
            "Bounds for context: {}",
            format!("function {}(..)", self.ctx.associated_fn_name(analyzer)).fg(Color::Cyan)
        )
    }

    fn labels(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            self.ctx_loc.source(),
            self.ctx_loc.start(),
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
        let mut reports = vec![report.finish()];

        reports.extend(
            self.vars_by_ctx
                .iter()
                .map(|(ctx, analyses)| {
                    let bounds_string = ctx
                        .ctx_deps(analyzer)
                        .iter()
                        .filter_map(|(_name, cvar)| {
                            let min = if self.report_config.eval_bounds {
                                cvar.range(analyzer)?
                                    .range_min()
                                    .eval(analyzer)
                                    .to_range_string(analyzer)
                                    .s
                            } else if self.report_config.simplify_bounds {
                                cvar.range(analyzer)?
                                    .range_min()
                                    .simplify(analyzer)
                                    .to_range_string(analyzer)
                                    .s
                            } else {
                                cvar.range(analyzer)?
                                    .range_min()
                                    .to_range_string(analyzer)
                                    .s
                            };

                            let max = if self.report_config.eval_bounds {
                                cvar.range(analyzer)?
                                    .range_max()
                                    .eval(analyzer)
                                    .to_range_string(analyzer)
                                    .s
                            } else if self.report_config.simplify_bounds {
                                cvar.range(analyzer)?
                                    .range_max()
                                    .simplify(analyzer)
                                    .to_range_string(analyzer)
                                    .s
                            } else {
                                cvar.range(analyzer)?
                                    .range_max()
                                    .to_range_string(analyzer)
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
                    let mut report = Report::build(
                        self.report_kind(),
                        self.ctx_loc.source(),
                        self.ctx_loc.start(),
                    )
                    .with_message(format!(
                        "Bounds for subcontext: {}{}{}",
                        ctx.path(analyzer).fg(Color::Cyan),
                        if bounds_string.is_empty() {
                            ""
                        } else {
                            " where "
                        },
                        bounds_string.fg(Color::Yellow),
                    ))
                    .with_config(
                        Config::default()
                            .with_cross_gap(false)
                            .with_underlines(true)
                            .with_tab_width(4),
                    );
                    let labels: Vec<_> = analyses
                        .iter()
                        .flat_map(|analysis| analysis.labels(analyzer))
                        .collect();

                    report.add_labels(labels);

                    if let Some((loc, var)) = ctx.return_node(analyzer) {
                        // println!("context {} had return", ctx.path(analyzer));
                        report.add_label(
                            Label::new(LocStrSpan::new(self.file_mapping, loc))
                                .with_message(
                                    &format!(
                                        "returns: \"{}\" ∈ {{{}, {}}}",
                                        var.display_name(analyzer),
                                        var.range(analyzer)
                                            .expect("return had no range")
                                            .range_min()
                                            .eval(analyzer)
                                            .to_range_string(analyzer)
                                            .s,
                                        var.range(analyzer)
                                            .expect("return had no range")
                                            .range_max()
                                            .eval(analyzer)
                                            .to_range_string(analyzer)
                                            .s,
                                    )
                                    .fg(Color::Yellow),
                                )
                                .with_color(Color::Yellow),
                        );
                    } else {
                        // println!("context {} did not have a return", ctx.path(analyzer));
                    }
                    report.finish()
                })
                .collect::<Vec<Report<LocStrSpan>>>(),
        );

        reports
    }

    fn print_reports(&self, src: (String, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = &self.reports(analyzer);
        for report in reports.into_iter() {
            let mut st = std::io::BufWriter::new(Vec::new());
            report.write((src.0.clone(), Source::from(src.1)), &mut st);
            println!("{}", String::from_utf8(st.into_inner().unwrap()).unwrap());
        }
    }

    fn eprint_reports(&self, src: (String, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = &self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.eprint((src.0.clone(), Source::from(src.1))).unwrap();
        });
    }
}

impl<T> FunctionVarsBoundAnalyzer for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait FunctionVarsBoundAnalyzer: BoundAnalyzer + Search + AnalyzerLike + Sized {
    fn bounds_for_all<'a>(
        &'a self,
        file_mapping: &'a BTreeMap<usize, String>,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        println!("{:?}", ctx.terminal_child_list(self));
        let analyses = ctx
            .terminal_child_list(self)
            .iter()
            .map(|child| {
                let mut parents = child.parent_list(self);
                parents.reverse();
                parents.push(*child);
                parents
                    .iter()
                    .for_each(|parent| println!("{}", parent.path(self)));
                println!("parents: {:?}", parents);
                let mut vars = ctx.vars(self);
                vars.sort_by(|a, b| a.name(self).cmp(&b.name(self)));
                vars.dedup_by(|a, b| a.name(self) == b.name(self));
                (
                    *child,
                    vars.iter()
                        .filter_map(|var| {
                            let name = var.name(self);
                            if report_config.show_tmps && report_config.show_consts {
                                Some(self.bounds_for_var_in_family_tree(
                                    file_mapping,
                                    parents.clone(),
                                    name,
                                    report_config,
                                ))
                            } else if report_config.show_tmps && !var.is_const(self) {
                                Some(self.bounds_for_var_in_family_tree(
                                    file_mapping,
                                    parents.clone(),
                                    name,
                                    report_config,
                                ))
                            } else if report_config.show_consts && !var.is_tmp(self) {
                                Some(self.bounds_for_var_in_family_tree(
                                    file_mapping,
                                    parents.clone(),
                                    name,
                                    report_config,
                                ))
                            } else if !var.is_tmp(self) && !var.is_const(self) {
                                Some(self.bounds_for_var_in_family_tree(
                                    file_mapping,
                                    parents.clone(),
                                    name,
                                    report_config,
                                ))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<BoundAnalysis>>(),
                )
            })
            .collect::<BTreeMap<ContextNode, Vec<BoundAnalysis>>>();

        FunctionVarsBoundAnalysis {
            file_mapping,
            ctx_loc: LocStrSpan::new(&file_mapping, ctx.underlying(self).loc),
            ctx,
            ctx_killed: if let Some(loc) = ctx.killed_loc(self) {
                Some(LocStrSpan::new(&file_mapping, loc))
            } else {
                None
            },
            vars_by_ctx: analyses,
            report_config,
        }
        // todo!()
    }
}
