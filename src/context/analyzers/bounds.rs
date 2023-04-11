use crate::analyzers::LocSpan;
use crate::analyzers::{LocStrSpan, ReportConfig, ReportDisplay};
use shared::{
    analyzer::{AnalyzerLike, Search},
    context::*,
    range::{range_string::*, Range, RangeEval, SolcRange},
};


use ariadne::{Cache, Color, Config, Fmt, Label, Report, ReportKind, Span};
use solang_parser::pt::{CodeLocation, StorageLocation};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct BoundAnalysis {
    pub ctx: ContextNode,
    pub var_name: String,
    pub var_display_name: String,
    pub var_def: (LocStrSpan, Option<SolcRange>),
    pub func_span: Option<LocStrSpan>,
    pub storage: Option<StorageLocation>,
    pub bound_changes: Vec<(LocStrSpan, SolcRange)>,
    pub report_config: ReportConfig,
    pub sub_ctxs: Vec<Self>,
    pub ctx_killed: Option<LocStrSpan>,
}

impl Default for BoundAnalysis {
    fn default() -> Self {
        Self {
            ctx: ContextNode(0),
            var_name: Default::default(),
            var_display_name: Default::default(),
            var_def: Default::default(),
            func_span: Default::default(),
            bound_changes: Default::default(),
            report_config: Default::default(),
            sub_ctxs: Default::default(),
            storage: None,
            ctx_killed: None,
        }
    }
}

static MIN_COLOR: Color = Color::Fixed(111);
static MAX_COLOR: Color = Color::Fixed(106);

#[derive(PartialEq, Eq, Clone)]
pub struct AnalysisItem {
    pub init: bool,
    pub order: i32,
    pub name: String,
    pub loc: LocStrSpan,
    pub storage: Option<StorageLocation>,
    pub ctx: ContextNode,
    pub ctx_conditionals: Vec<(String, Vec<RangePart>)>,
    pub parts: Vec<RangePart>,
    pub unsat: bool,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct StrippedAnalysisItem {
    pub init: bool,
    pub order: i32,
    pub name: String,
    pub loc: LocSpan,
    // pub storage: Option<StorageLocation>,
    pub ctx: ContextNode,
    pub ctx_conditionals: Vec<(String, Vec<RangePart>)>,
    pub parts: Vec<RangePart>,
    pub unsat: bool,
}

impl From<AnalysisItem> for StrippedAnalysisItem {
    fn from(ai: AnalysisItem) -> Self {
        Self {
            init: ai.init,
            order: ai.order,
            name: ai.name,
            loc: LocSpan(ai.loc.1),
            // storage: ai.storage,
            ctx: ai.ctx,
            ctx_conditionals: ai.ctx_conditionals,
            parts: ai.parts,
            unsat: ai.unsat,
        }
    }
}

impl PartialOrd for StrippedAnalysisItem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for StrippedAnalysisItem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.loc.0.cmp(&other.loc.0)
    }
}

#[derive(Default, Clone, Debug, Hash)]
pub struct OrderedAnalysis {
    pub analyses: BTreeMap<usize, BTreeSet<StrippedAnalysisItem>>,
}

impl OrderedAnalysis {
    pub fn from_bound_analysis(ba: BoundAnalysis, analyzer: &(impl AnalyzerLike + Search)) -> Self {
        let mut analyses: BTreeMap<usize, BTreeSet<StrippedAnalysisItem>> = Default::default();
        if let Some(init) = ba.init_item(analyzer) {
            let source: usize = *LocSpan(init.loc.1).source();
            let mut set = BTreeSet::new();
            set.insert(init.into());
            analyses.insert(source, set);
        }
        ba.bound_changes
            .iter()
            .enumerate()
            .for_each(|(i, bound_change)| {
                let (parts, unsat) = ba.range_parts(analyzer, &bound_change.1);
                let item = StrippedAnalysisItem {
                    init: false,
                    name: ba.var_display_name.clone(),
                    loc: LocSpan(bound_change.0 .1),
                    order: i as i32,
                    // storage: ba.storage.clone(),
                    ctx: ba.ctx,
                    ctx_conditionals: ba.conditionals(analyzer),
                    parts,
                    unsat,
                };

                let entry = analyses
                    .entry(*LocSpan(bound_change.0 .1).source())
                    .or_default();
                entry.insert(item);
            });
        Self { analyses }
    }

    pub fn from_func_analysis(
        fvba: FunctionVarsBoundAnalysis,
        analyzer: &(impl AnalyzerLike + Search),
    ) -> Self {
        let mut analyses = Self::default();
        fvba.vars_by_ctx.iter().for_each(|(_ctx, bas)| {
            bas.iter().for_each(|ba| {
                analyses.extend(Self::from_bound_analysis(ba.clone(), analyzer));
            })
        });
        analyses
    }

    pub fn extend(&mut self, other: Self) {
        other.analyses.into_iter().for_each(|(key, set)| {
            let entry = self.analyses.entry(key).or_default();
            entry.extend(set);
        });
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Hash)]
pub enum RangePart {
    Equal(String),
    Inclusion(String, String),
    Exclusion(Vec<RangePart>),
}

impl RangePart {
    pub fn to_cli_string(self) -> String {
        match self {
            RangePart::Equal(val) => format!(" == {}", val),
            RangePart::Inclusion(min, max) => {
                format!(" ∈ [ {}, {} ]", min.fg(MIN_COLOR), max.fg(MAX_COLOR))
            }
            RangePart::Exclusion(parts) => format!(
                "&& ∉ {{{}}}",
                parts
                    .into_iter()
                    .map(|p| p.to_cli_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
            .fg(Color::Red)
            .to_string(),
        }
    }

    pub fn to_normal_string(&self) -> String {
        match self {
            e @ RangePart::Equal(_) => format!(" == {}", e.to_string()),
            e @ RangePart::Inclusion(..) => format!(" ∈ {}", e.to_string()),
            e @ RangePart::Exclusion(_) => format!("&& ∉ {{{}}}", e.to_string()),
        }
    }
}

impl Into<Label<LocStrSpan>> for AnalysisItem {
    fn into(self) -> ariadne::Label<LocStrSpan> {
        let (color, order, priority) = if self.init {
            (Color::Magenta, self.order, -1)
        } else {
            (
                match self.storage {
                    Some(StorageLocation::Memory(..)) => Color::Blue,
                    Some(StorageLocation::Storage(..)) => Color::Green,
                    Some(StorageLocation::Calldata(..)) => Color::White,
                    None => Color::Cyan,
                },
                self.order,
                0,
            )
        };

        Label::new(self.loc)
            .with_message(format!(
                "{}\"{}\"{}{}",
                match self.storage {
                    Some(StorageLocation::Memory(..)) => "Memory var ",
                    Some(StorageLocation::Storage(..)) => "Storage var ",
                    Some(StorageLocation::Calldata(..)) => "Calldata var ",
                    None => "",
                },
                self.name,
                self.parts
                    .into_iter()
                    .map(|part| part.to_cli_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                if self.unsat {
                    " - unsatisfiable range, unreachable".fg(Color::Red)
                } else {
                    "".fg(Color::Red)
                }
            ))
            .with_color(color)
            .with_order(order)
            .with_priority(priority)
    }
}

impl ToString for StrippedAnalysisItem {
    fn to_string(&self) -> String {
        format!(
            "{}{}{}",
            // match self.storage {
            //     Some(StorageLocation::Memory(..)) => "Memory var ",
            //     Some(StorageLocation::Storage(..)) => "Storage var ",
            //     Some(StorageLocation::Calldata(..)) => "Calldata var ",
            //     None => "",
            // },
            self.name,
            self.parts
                .iter()
                .map(|part| part.to_normal_string())
                .collect::<Vec<_>>()
                .join(" "),
            if self.unsat {
                " - unsatisfiable range, unreachable"
            } else {
                ""
            }
        )
    }
}

impl ToString for RangePart {
    fn to_string(&self) -> String {
        match self {
            RangePart::Equal(inner) => inner.to_string(),
            RangePart::Inclusion(min, max) => format!("[ {}, {} ]", min, max),
            RangePart::Exclusion(inner) => format!(
                "{{{}}}",
                inner
                    .iter()
                    .map(|part| part.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl BoundAnalysis {
    pub fn conditionals(
        &self,
        analyzer: &(impl AnalyzerLike + Search),
    ) -> Vec<(String, Vec<RangePart>)> {
        let deps = self.ctx.ctx_deps(analyzer);
        let deps = deps
            .values()
            .map(|var| (var.display_name(analyzer), var))
            .collect::<BTreeMap<_, _>>();
        // create the bound strings
        deps.iter()
            .enumerate()
            .filter_map(|(_i, (_name, cvar))| {
                let range = cvar.range(analyzer)?;
                let parts = self.range_parts(analyzer, &range).0;
                Some((cvar.display_name(analyzer), parts))
            })
            .collect()
    }
    pub fn range_parts(
        &self,
        analyzer: &(impl AnalyzerLike + Search),
        range: &SolcRange,
    ) -> (Vec<RangePart>, bool) {
        let mut parts = vec![];
        let min = if self.report_config.eval_bounds {
            range
                .evaled_range_min(analyzer)
                .to_range_string(false, analyzer)
                .s
        } else if self.report_config.simplify_bounds {
            range
                .simplified_range_min(analyzer)
                .to_range_string(false, analyzer)
                .s
        } else {
            range.range_min().to_range_string(false, analyzer).s
        };
        let max = if self.report_config.eval_bounds {
            range
                .evaled_range_max(analyzer)
                .to_range_string(true, analyzer)
                .s
        } else if self.report_config.simplify_bounds {
            range
                .simplified_range_max(analyzer)
                .to_range_string(true, analyzer)
                .s
        } else {
            range.range_max().to_range_string(true, analyzer).s
        };

        if min == max {
            parts.push(RangePart::Equal(min));
        } else {
            parts.push(RangePart::Inclusion(min, max));
        }

        let range_excl = range.range_exclusions();
        if !range_excl.is_empty() {
            parts.push(RangePart::Exclusion(
                range_excl
                    .iter()
                    .map(|range| {
                        let min = range.to_range_string(false, analyzer).s;
                        let max = range.to_range_string(true, analyzer).s;

                        if min == max {
                            RangePart::Equal(min)
                        } else {
                            RangePart::Inclusion(min, max)
                        }
                    })
                    .collect::<Vec<_>>(),
            ));
        }
        let unsat = range.unsat(analyzer);
        (parts, unsat)
    }

    pub fn init_item(&self, analyzer: &(impl AnalyzerLike + Search)) -> Option<AnalysisItem> {
        let mut parts = vec![];
        let mut unsat = false;
        if let Some(init_range) = &self.var_def.1 {
            (parts, unsat) = self.range_parts(analyzer, init_range)
        }
        if parts.is_empty() {
            None
        } else {
            Some(AnalysisItem {
                init: true,
                order: -1,
                name: self.var_display_name.clone(),
                loc: self.var_def.0.clone(),
                storage: self.storage.clone(),
                ctx: self.ctx,
                ctx_conditionals: self.conditionals(analyzer),
                parts,
                unsat,
            })
        }
    }

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
        let entry = map.entry(self.ctx).or_default();
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
                    if self.var_def.1.is_some() && sub_analysis.var_def.1.is_none() {
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
            let entry = map.entry(self.ctx).or_default();
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
            let entry = map.entry(self.ctx).or_default();
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
                    let (parts, unsat) = self.range_parts(analyzer, &bound_change.1);
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

        if let Some(killed_span) = &self.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message("Execution guaranteed to revert here!".fg(Color::Red))
                    .with_color(Color::Red),
            );
        }

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

    fn print_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &(impl AnalyzerLike + Search),
    ) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.print(&mut src).unwrap();
        });
    }

    fn eprint_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &(impl AnalyzerLike + Search),
    ) {
        let reports = self.reports(analyzer);
        reports.into_iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}

impl<T> BoundAnalyzer for T where T: Search + AnalyzerLike + Sized {}
pub trait BoundAnalyzer: Search + AnalyzerLike + Sized {
    fn bounds_for_var_in_family_tree(
        &self,
        file_mapping: &'_ BTreeMap<usize, String>,
        ordered_ctxs: Vec<ContextNode>,
        var_name: String,
        report_config: ReportConfig,
    ) -> BoundAnalysis {
        let mut inherited = None;
        ordered_ctxs
            .into_iter()
            .filter_map(|ctx| Some((ctx, ctx.var_by_name(self, &var_name)?)))
            .for_each(|(_ctx, cvar)| {
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

    fn bounds_for_var(
        &self,
        inherited: Option<BoundAnalysis>,
        file_mapping: &'_ BTreeMap<usize, String>,
        ctx: ContextNode,
        var_name: String,
        report_config: ReportConfig,
        is_subctx: bool,
    ) -> Vec<(bool, BoundAnalysis)> {
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
    fn bounds_for_var_node(
        &self,
        inherited: Option<BoundAnalysis>,
        file_mapping: &'_ BTreeMap<usize, String>,
        var_name: String,
        cvar: ContextVarNode,
        report_config: ReportConfig,
        is_subctx: bool,
    ) -> BoundAnalysis {
        let mut curr = cvar.first_version(self);

        let ctx = cvar.ctx(self);
        let func_span = if let Some(fn_call) = ctx.underlying(self).fn_call {
            Some(LocStrSpan::new(file_mapping, fn_call.underlying(self).loc))
        } else {
            Some(LocStrSpan::new(
                file_mapping,
                ctx.underlying(self).parent_fn.underlying(self).loc,
            ))
        };

        let mut ba = if let Some(inherited) = inherited {
            let mut new_ba = inherited;
            new_ba.ctx = ctx;
            new_ba.func_span = func_span;
            new_ba.ctx_killed = ctx
                .killed_loc(self)
                .map(|loc| LocStrSpan::new(file_mapping, loc));
            new_ba
        } else {
            BoundAnalysis {
                ctx,
                var_name,
                var_display_name: cvar.display_name(self),
                func_span,
                var_def: (
                    LocStrSpan::new(file_mapping, curr.loc(self)),
                    if !is_subctx { curr.range(self) } else { None },
                ),
                bound_changes: vec![],
                report_config,
                sub_ctxs: vec![],
                storage: curr.underlying(self).storage.clone(),
                ctx_killed: ctx
                    .killed_loc(self)
                    .map(|loc| LocStrSpan::new(file_mapping, loc)),
            }
        };

        if let Some(curr_range) = curr.range(self) {
            let mut cr_min = curr_range.evaled_range_min(self);
            let mut cr_max = curr_range.evaled_range_max(self);
            let mut cr_excl = curr_range.range_exclusions();
            while let Some(next) = curr.next_version(self) {
                if let Some(next_range) = next.range(self) {
                    let nr_min = next_range.evaled_range_min(self);
                    let nr_max = next_range.evaled_range_max(self);
                    let nr_excl = next_range.exclusions.clone();

                    if report_config.show_all_lines
                        || nr_min != cr_min
                        || nr_max != cr_max
                        || nr_excl != cr_excl
                    {
                        cr_min = nr_min;
                        cr_max = nr_max;
                        cr_excl = nr_excl;
                        ba.bound_changes.push((
                            LocStrSpan::new(file_mapping, next.loc(self)),
                            next_range.clone(),
                        ));
                    }
                }

                if next == cvar {
                    break;
                } else {
                    curr = next;
                }
            }
        }

        ba
    }
}

#[derive(Debug, Clone)]
pub struct FunctionVarsBoundAnalysis {
    pub ctx_loc: LocStrSpan,
    pub ctx: ContextNode,
    pub ctx_killed: Option<LocStrSpan>,
    pub report_config: ReportConfig,
    pub vars_by_ctx: BTreeMap<ContextNode, Vec<BoundAnalysis>>,
}

impl<'a> FunctionVarsBoundAnalysis {
    pub fn as_cli_compat(
        self,
        file_mapping: &'a BTreeMap<usize, String>,
    ) -> CLIFunctionVarsBoundAnalysis<'a> {
        CLIFunctionVarsBoundAnalysis::new(file_mapping, self)
    }
}

pub struct CLIFunctionVarsBoundAnalysis<'a> {
    pub file_mapping: &'a BTreeMap<usize, String>,
    pub func_var_bound_analysis: FunctionVarsBoundAnalysis,
}

impl<'a> CLIFunctionVarsBoundAnalysis<'a> {
    pub fn new(
        file_mapping: &'a BTreeMap<usize, String>,
        func_var_bound_analysis: FunctionVarsBoundAnalysis,
    ) -> Self {
        Self {
            file_mapping,
            func_var_bound_analysis,
        }
    }
}

impl<'a> ReportDisplay for CLIFunctionVarsBoundAnalysis<'a> {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Bounds", Color::Cyan)
    }
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String {
        format!(
            "Bounds for function: {}",
            format!(
                "function {}",
                self.func_var_bound_analysis
                    .ctx
                    .associated_fn_name(analyzer)
            )
            .fg(Color::Cyan)
        )
    }

    fn labels(&self, _analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocStrSpan>> {
        let mut report = Report::build(
            self.report_kind(),
            self.func_var_bound_analysis.ctx_loc.source(),
            self.func_var_bound_analysis.ctx_loc.start(),
        )
        .with_message(self.msg(analyzer))
        .with_config(
            Config::default()
                .with_cross_gap(false)
                .with_underlines(true)
                .with_tab_width(4),
        );

        report.add_labels(self.labels(analyzer));
        if let Some(killed_span) = &self.func_var_bound_analysis.ctx_killed {
            report = report.with_label(
                Label::new(killed_span.clone())
                    .with_message("Execution guaranteed to revert here!".fg(Color::Red))
                    .with_color(Color::Red),
            );
        }

        let mut reports = vec![report.finish()];

        let mut called_fns = BTreeSet::new();
        let mut added_fn_calls = BTreeSet::new();
        let mut called_contracts = BTreeSet::new();
        let mut called_external_fns = BTreeSet::new();

        reports.extend(
            self.func_var_bound_analysis
                .vars_by_ctx
                .iter()
                .map(|(ctx, analyses)| {
                    // sort by display name instead of normal name
                    let deps = ctx.ctx_deps(analyzer);
                    let deps = deps
                        .values()
                        .map(|var| (var.display_name(analyzer), var))
                        .collect::<BTreeMap<_, _>>();
                    // create the bound strings
                    let bounds_string = deps
                        .iter()
                        .enumerate()
                        .filter_map(|(i, (_name, cvar))| {
                            let min = if self.func_var_bound_analysis.report_config.eval_bounds {
                                cvar.range(analyzer)?
                                    .evaled_range_min(analyzer)
                                    .to_range_string(false, analyzer)
                                    .s
                            } else if self.func_var_bound_analysis.report_config.simplify_bounds {
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

                            let max = if self.func_var_bound_analysis.report_config.eval_bounds {
                                cvar.range(analyzer)?
                                    .evaled_range_max(analyzer)
                                    .to_range_string(true, analyzer)
                                    .s
                            } else if self.func_var_bound_analysis.report_config.simplify_bounds {
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
                            if min == max {
                                Some(format!(
                                    "  {}. {} == {}\n",
                                    i + 1,
                                    cvar.display_name(analyzer),
                                    min
                                ))
                            } else {
                                Some(format!(
                                    "  {}. \"{}\" ∈ [ {}, {} ]\n",
                                    i + 1,
                                    cvar.display_name(analyzer),
                                    min.fg(MIN_COLOR),
                                    max.fg(MAX_COLOR),
                                ))
                            }
                        })
                        .collect::<Vec<_>>()
                        .join("");
                    let mut report = Report::build(
                        self.report_kind(),
                        self.func_var_bound_analysis.ctx_loc.source(),
                        self.func_var_bound_analysis.ctx_loc.start(),
                    )
                    .with_message(format!(
                        "Bounds for subcontext: {}{}{}",
                        ctx.path(analyzer).fg(Color::Cyan),
                        if bounds_string.is_empty() {
                            ""
                        } else {
                            " where:\n"
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

                    if let Some(killed_span) = &self.func_var_bound_analysis.ctx_killed {
                        report = report.with_label(
                            Label::new(killed_span.clone())
                                .with_message("Execution guaranteed to revert here!".fg(Color::Red))
                                .with_color(Color::Red),
                        );
                    }

                    if !added_fn_calls.contains(ctx) {
                        ctx.underlying(analyzer)
                            .children
                            .iter()
                            .filter(|child| child.underlying(analyzer).fn_call.is_some())
                            .for_each(|child| {
                                report.add_label(
                                    Label::new(LocStrSpan::new(
                                        self.file_mapping,
                                        child.underlying(analyzer).loc,
                                    ))
                                    .with_color(Color::Fixed(140))
                                    .with_order(5),
                                );
                            });

                        added_fn_calls.insert(ctx);
                    }

                    ctx.return_nodes(analyzer)
                        .into_iter()
                        .for_each(|(loc, var)| {
                            if let Some(range) = var.range(analyzer) {
                                let min = range
                                    .evaled_range_min(analyzer)
                                    .to_range_string(false, analyzer)
                                    .s;
                                let max = range
                                    .evaled_range_max(analyzer)
                                    .to_range_string(true, analyzer)
                                    .s;
                                let r_str = if min == max {
                                    format!(" == {}", min.fg(MAX_COLOR))
                                } else {
                                    format!(" ∈ [ {}, {} ]", min.fg(MIN_COLOR), max.fg(MAX_COLOR),)
                                };
                                report.add_label(
                                    Label::new(LocStrSpan::new(self.file_mapping, loc))
                                        .with_message(
                                            format!(
                                                "returns: \"{}\"{}",
                                                var.display_name(analyzer),
                                                r_str
                                            )
                                            .fg(Color::Yellow),
                                        )
                                        .with_color(Color::Yellow)
                                        .with_order(3),
                                );
                            }
                        });

                    if let Some(body) = ctx.underlying(analyzer)
                            .parent_fn
                            .underlying(analyzer)
                            .body
                            .as_ref() {
                        report.add_label(
                            Label::new(LocStrSpan::new(
                                self.file_mapping,
                                body.loc(),
                            ))
                            .with_message("Entry function call")
                            .with_priority(-2)
                            .with_order(-2),
                        );
                                
                    }
                    

                    ctx.underlying(analyzer).children.iter().for_each(|child| {
                        if let Some(fn_call) = child.underlying(analyzer).fn_call {
                            let fn_name = fn_call.name(analyzer);
                            if !called_fns.contains(&fn_name) {
                                if let Some(body) = fn_call
                                            .underlying(analyzer)
                                            .body
                                            .as_ref() {
                                    report.add_label(
                                        Label::new(LocStrSpan::new(
                                            self.file_mapping,
                                            body.loc(),
                                        ))
                                        .with_message("Internal function call")
                                        .with_priority(-2)
                                        .with_order(-2)
                                        .with_color(Color::Fixed(140)),
                                    );         
                                }
                                
                                called_fns.insert(fn_name);
                            }
                        }

                        if let Some(ext_fn_call) = child.underlying(analyzer).ext_fn_call {
                            let fn_name = ext_fn_call.name(analyzer);
                            if !called_external_fns.contains(&fn_name) {
                                if let Some(body) = &ext_fn_call.underlying(analyzer).body {
                                    report.add_label(
                                        Label::new(LocStrSpan::new(self.file_mapping, body.loc()))
                                            .with_message("External function call")
                                            .with_priority(-2)
                                            .with_order(-2)
                                            .with_color(Color::Fixed(75)),
                                    );
                                }

                                called_external_fns.insert(fn_name);
                            }

                            if let Some(c) = ext_fn_call.maybe_associated_contract(analyzer) {
                                if let Some(cname) = c.maybe_name(analyzer) {
                                    if !called_contracts.contains(&cname) {
                                        report.add_label(
                                            Label::new(LocStrSpan::new(
                                                self.file_mapping,
                                                c.loc(analyzer),
                                            ))
                                            .with_message("External Contract")
                                            .with_priority(-3)
                                            .with_order(-3)
                                            .with_color(Color::Fixed(8)),
                                        );

                                        called_contracts.insert(cname);
                                    }
                                }
                            }
                        }

                        child
                            .return_nodes(analyzer)
                            .into_iter()
                            .for_each(|(loc, var)| {
                                if let Some(range) = var.range(analyzer) {
                                    let min = range
                                        .evaled_range_min(analyzer)
                                        .to_range_string(false, analyzer)
                                        .s;
                                    let max = range
                                        .evaled_range_max(analyzer)
                                        .to_range_string(true, analyzer)
                                        .s;
                                    let r_str = if min == max {
                                        format!(" == {}", min.fg(MAX_COLOR))
                                    } else {
                                        format!(
                                            " ∈ [ {}, {} ]",
                                            min.fg(MIN_COLOR),
                                            max.fg(MAX_COLOR),
                                        )
                                    };
                                    report.add_label(
                                        Label::new(LocStrSpan::new(self.file_mapping, loc))
                                            .with_message(
                                                format!(
                                                    "returns: \"{}\"{}",
                                                    var.display_name(analyzer),
                                                    r_str
                                                )
                                                .fg(Color::Yellow),
                                            )
                                            .with_color(Color::Yellow)
                                            .with_order(3),
                                    );
                                }
                            })
                    });
                    report.finish()
                })
                .collect::<Vec<Report<LocStrSpan>>>(),
        );

        reports
    }

    fn print_reports(
        &self,
        mut src: &mut impl Cache<String>,
        analyzer: &(impl AnalyzerLike + Search),
    ) {
        let reports = &self.reports(analyzer);
        for report in reports.iter() {
            report.print(&mut src).unwrap();
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

impl<T> FunctionVarsBoundAnalyzer for T where T: BoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait FunctionVarsBoundAnalyzer: BoundAnalyzer + Search + AnalyzerLike + Sized {
    fn bounds_for_all<'a>(
        &'a self,
        file_mapping: &'a BTreeMap<usize, String>,
        ctx: ContextNode,
        report_config: ReportConfig,
    ) -> FunctionVarsBoundAnalysis {
        let analyses = ctx
            .terminal_child_list(self)
            .iter()
            .map(|child| {
                let mut parents = child.parent_list(self);
                parents.reverse();
                parents.push(*child);
                let _children: Vec<_> = parents
                    .iter()
                    .flat_map(|p| p.returning_child_list(self))
                    .collect();
                let mut vars = ctx.vars(self);
                vars.sort_by_key(|a| a.name(self));
                vars.dedup_by(|a, b| a.name(self) == b.name(self));
                (
                    *child,
                    vars.iter()
                        .filter_map(|var| {
                            let name = var.name(self);

                            let is_ret = var.is_return_node_in_any(&parents, self);
                            if is_ret | report_config.show_tmps | report_config.show_initial_bounds
                                && report_config.show_consts | report_config.show_tmps
                                && !var.is_const(self) | report_config.show_consts
                                && !var.is_tmp(self) | !var.is_tmp(self)
                                && !var.is_const(self)
                            {
                                // println!("var: {}", name);
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
            ctx_loc: LocStrSpan::new(file_mapping, ctx.underlying(self).loc),
            ctx,
            ctx_killed: ctx
                .killed_loc(self)
                .map(|loc| LocStrSpan::new(file_mapping, loc)),
            vars_by_ctx: analyses,
            report_config,
        }
    }
}
