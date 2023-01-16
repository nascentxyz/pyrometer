use crate::range::BuiltinRange;
use crate::range::ElemEval;
use crate::range::RangeEval;
use crate::range::RangeSize;
use crate::range::ToRangeString;
use crate::{
    AnalyzerLike, ContextNode, ContextVarNode, LocSpan, ReportConfig, ReportDisplay, Search,
};

use ariadne::{Color, Config, Fmt, Label, Report, ReportKind, Source, Span};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct BoundAnalysis {
    pub ctx: ContextNode,
    pub var_name: String,
    pub var_display_name: String,
    pub var_def: (LocSpan, Option<BuiltinRange>),
    pub storage: bool,
    pub bound_changes: Vec<(LocSpan, BuiltinRange)>,
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
    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>> {
        let mut labels = if self.report_config.show_initial_bounds {
            if let Some(init_range) = &self.var_def.1 {
                vec![Label::new(self.var_def.0)
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
                        } else {
                            init_range.range_min().to_range_string(analyzer).s
                        },
                        if self.report_config.eval_bounds {
                            init_range
                                .range_max()
                                .eval(analyzer)
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
                    } else {
                        bound_change.1.range_max().to_range_string(analyzer).s
                    };

                    Label::new(bound_change.0)
                        .with_message(format!(
                            "{}\"{}\" ∈ {{{}, {}}} {}",
                            if self.storage { "storage var " } else { "" },
                            self.var_display_name,
                            min,
                            max,
                            if bound_change.1.unsat(analyzer) {
                                "- unsatisfiable range, would revert".fg(Color::Red)
                            } else {
                                "".fg(Color::Red)
                            }
                        ))
                        .with_color(Color::Cyan)
                })
                .collect::<Vec<_>>(),
        );

        labels
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            *self.var_def.0.source(),
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

    fn print_reports(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print((src.0, Source::from(src.1))).unwrap();
        });
    }
}

impl<T> BoundAnalyzer for T where T: Search + AnalyzerLike + Sized {}
pub trait BoundAnalyzer: Search + AnalyzerLike + Sized {
    fn bounds_for_var(
        &self,
        ctx: ContextNode,
        var_name: String,
        report_config: ReportConfig,
    ) -> Option<BoundAnalysis> {
        let cvar = ctx.var_by_name(self, &var_name)?;
        let mut analysis = self.bounds_for_var_node(var_name.clone(), cvar, report_config);
        if report_config.show_subctxs {
            let mut subctxs = ctx.subcontexts(self);
            subctxs.sort();
            subctxs.dedup();
            let curr = cvar.ctx(self);
            let subctx_bounds = subctxs
                .into_iter()
                .filter(|sub_ctx| *sub_ctx != curr)
                .filter_map(|sub_ctx| self.bounds_for_var(sub_ctx, var_name.clone(), report_config))
                .collect::<Vec<_>>();
            analysis.sub_ctxs = subctx_bounds;
            Some(analysis)
        } else {
            Some(analysis)
        }
    }

    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node(
        &self,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        println!("bounds for var: {}", var_name);
        let mut curr = cvar.first_version(self);

        let mut ba = BoundAnalysis {
            ctx: cvar.ctx(self),
            var_name,
            var_display_name: cvar.display_name(self),
            var_def: (LocSpan(curr.loc(self)), curr.range(self)),
            bound_changes: vec![],
            report_config,
            sub_ctxs: vec![],
            storage: curr.underlying(self).storage.is_some(),
        };

        if let Some(mut curr_range) = curr.range(self) {
            while let Some(next) = curr.next_version(self) {
                if let Some(next_range) = next.range(self) {
                    if next_range != curr_range {
                        ba.bound_changes
                            .push((LocSpan(next.loc(self)), next_range.clone()));
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

    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node_and_dependents(
        &self,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        // let bounds = self.bounds_for_var_node(var_name, cvar, report_config);
        // let mut dependents = cvar.dependent_on(self, false);
        // dependents.sort_by(|a, b| a.display_name(self).cmp(&b.display_name(self)));
        // dependents.dedup_by(|a, b| a.display_name(self) == b.display_name(self));

        // let dep_bounds = dependents
        //     .into_iter()
        //     .filter_map(
        //         |var| match (report_config.show_tmps, report_config.show_consts) {
        //             (true, true) => {
        //                 let name = var.name(self);
        //                 Some(self.bounds_for_var_node(name, var, report_config))
        //             }
        //             (true, false) => {
        //                 if !var.is_tmp(self) {
        //                     let name = var.name(self);
        //                     Some(self.bounds_for_var_node(name, var, report_config))
        //                 } else {
        //                     None
        //                 }
        //             }
        //             (false, true) => {
        //                 if !var.is_const(self) {
        //                     let name = var.name(self);
        //                     Some(self.bounds_for_var_node(name, var, report_config))
        //                 } else {
        //                     None
        //                 }
        //             }
        //             (false, false) => {
        //                 if !var.is_tmp(self) && !var.is_const(self) {
        //                     let name = var.name(self);
        //                     Some(self.bounds_for_var_node(name, var, report_config))
        //                 } else {
        //                     None
        //                 }
        //             }
        //         },
        //     )
        //     .collect();
        // (bounds, dep_bounds)
        todo!()
    }
}

#[derive(Debug, Clone)]
pub struct FunctionVarsBoundAnalysis {
    pub ctx_loc: LocSpan,
    pub ctx: ContextNode,
    pub ctx_killed: Option<LocSpan>,
    pub report_config: ReportConfig,
    pub vars_by_ctx: BTreeMap<ContextNode, Vec<BoundAnalysis>>,
}

impl ReportDisplay for FunctionVarsBoundAnalysis {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!(
            "Bounds for context: {}",
            format!("function {}(..)", self.ctx.associated_fn_name(analyzer)).fg(Color::Cyan)
        )
    }

    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            *self.ctx_loc.source(),
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
        if let Some(killed_span) = self.ctx_killed {
            report = report.with_label(
                Label::new(killed_span)
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
                        *self.ctx_loc.source(),
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
                        bounds_string.fg(Color::Yellow)
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
                        println!("context {} had return", ctx.path(analyzer));
                        report.add_label(
                            Label::new(LocSpan(loc))
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
                                    .fg(Color::Green),
                                )
                                .with_color(Color::Green),
                        );
                    } else {
                        println!("context {} did not have a return", ctx.path(analyzer));
                    }
                    report.finish()
                })
                .collect::<Vec<Report<LocSpan>>>(),
        );

        reports
    }

    fn print_reports(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search)) {
        let reports = &self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print((src.0, Source::from(src.1))).unwrap();
        });
    }
}

impl<T> FunctionVarsBoundAnalyzer for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait FunctionVarsBoundAnalyzer: BoundAnalyzer + Search + AnalyzerLike + Sized {
    fn bounds_for_all(
        &self,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        let mut vars = ctx.vars(self);
        println!("{:?}", vars);
        vars.dedup();

        let analyses: BTreeMap<ContextNode, Vec<BoundAnalysis>> = vars
            .into_iter()
            .filter_map(
                |var| match (report_config.show_tmps, report_config.show_consts) {
                    (true, true) => {
                        let name = var.name(self);
                        Some(
                            self.bounds_for_var(ctx, name, report_config)?
                                .flatten_by_ctx(),
                        )
                    }
                    (true, false) => {
                        if !var.is_const(self) {
                            let name = var.name(self);
                            Some(
                                self.bounds_for_var(ctx, name, report_config)?
                                    .flatten_by_ctx(),
                            )
                        } else {
                            None
                        }
                    }
                    (false, true) => {
                        if !var.is_tmp(self) {
                            let name = var.name(self);
                            Some(
                                self.bounds_for_var(ctx, name, report_config)?
                                    .flatten_by_ctx(),
                            )
                        } else {
                            None
                        }
                    }
                    (false, false) => {
                        if !var.is_tmp(self) && !var.is_const(self) {
                            let name = var.name(self);
                            Some(
                                self.bounds_for_var(ctx, name, report_config)?
                                    .flatten_by_ctx(),
                            )
                        } else {
                            None
                        }
                    }
                },
            )
            .fold(BTreeMap::default(), |mut map, var_analysis| {
                var_analysis.into_iter().for_each(|(ctx, analysis)| {
                    let entry: &mut Vec<BoundAnalysis> = map.entry(ctx).or_default();
                    entry.push(analysis);
                    entry.sort_by(|a, b| a.var_name.cmp(&b.var_name));
                    entry.dedup_by(|a, b| a.var_name == b.var_name);
                });

                map
            });
        FunctionVarsBoundAnalysis {
            ctx_loc: LocSpan(ctx.underlying(self).loc),
            ctx,
            ctx_killed: if let Some(loc) = ctx.killed_loc(self) {
                Some(LocSpan(loc))
            } else {
                None
            },
            vars_by_ctx: analyses,
            report_config,
        }
    }
}
