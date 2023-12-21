use crate::{
    bounds::{range_parts, AnalysisItem, RangePart},
    LocStrSpan, ReportConfig,
};

use graph::{
    nodes::{ContextNode, ContextVarNode, KilledKind},
    AnalyzerBackend, GraphBackend, Range, SolcRange,
};
use shared::{Search, StorageLocation};

use std::collections::BTreeSet;

use solang_parser::pt::CodeLocation;
use std::collections::BTreeMap;

mod report_display;

#[derive(PartialOrd, Eq, PartialEq, Ord, Clone, Debug)]
pub struct CtxSwitch {
    pub ctx: ContextNode,
    pub func_span: LocStrSpan,
    pub func_body_span: Option<LocStrSpan>,
    pub killed_loc: Option<(LocStrSpan, KilledKind)>,
}

#[derive(Debug, Clone)]
pub struct VarBoundAnalysis {
    /// The context to analyze
    pub ctx: ContextNode,
    /// The variable's name
    pub var_name: String,
    /// The variable's display name
    pub var_display_name: String,
    /// The variable definition and optionally it's initial range
    pub var_def: (LocStrSpan, Option<SolcRange>),
    /// The function defintion
    pub func_span: LocStrSpan,
    /// Storage type of the variable
    pub storage: Option<StorageLocation>,
    /// Vector of bound changes and their location
    pub bound_changes: Vec<(LocStrSpan, SolcRange)>,
    /// Report configuration
    pub report_config: ReportConfig,
    /// Spanned (context nodes, function name span, return spans)
    pub spanned_ctx_info: BTreeSet<CtxSwitch>,
    /// Location where context was killed
    pub ctx_killed: Option<(LocStrSpan, KilledKind)>,
}

impl Default for VarBoundAnalysis {
    fn default() -> Self {
        Self {
            ctx: ContextNode(0),
            var_name: Default::default(),
            var_display_name: Default::default(),
            var_def: Default::default(),
            func_span: Default::default(),
            bound_changes: Default::default(),
            report_config: Default::default(),
            storage: None,
            ctx_killed: None,
            spanned_ctx_info: Default::default(),
        }
    }
}

impl VarBoundAnalysis {
    pub fn conditionals(&self, analyzer: &impl GraphBackend) -> Vec<(String, Vec<RangePart>)> {
        let deps = self.ctx.ctx_deps(analyzer).unwrap();
        let deps = deps
            .iter()
            .map(|var| (var.display_name(analyzer).unwrap(), var))
            .collect::<BTreeMap<_, _>>();
        // create the bound strings
        deps.iter()
            .enumerate()
            .filter_map(|(_i, (_name, cvar))| {
                let range = cvar.ref_range(analyzer).unwrap()?;
                let parts = range_parts(analyzer, &self.report_config, &range).0;
                Some((cvar.display_name(analyzer).unwrap(), parts))
            })
            .collect()
    }

    /// Creates an [AnalysisItem] if there is a initial bound for a variable
    pub fn init_item(&self, analyzer: &impl GraphBackend) -> Option<AnalysisItem> {
        let mut parts = vec![];
        let mut unsat = false;
        if let Some(init_range) = &self.var_def.1 {
            (parts, unsat) = range_parts(analyzer, &self.report_config, init_range)
        }
        if parts.is_empty() {
            None
        } else {
            Some(AnalysisItem {
                init: true,
                order: -1,
                name: self.var_display_name.clone(),
                loc: self.var_def.0.clone(),
                storage: self.storage,
                ctx: self.ctx,
                ctx_conditionals: self.conditionals(analyzer),
                parts,
                unsat,
            })
        }
    }
}

impl<T> VarBoundAnalyzer for T where T: Search + AnalyzerBackend + Sized {}
pub trait VarBoundAnalyzer: Search + AnalyzerBackend + Sized {
    /// Given a lineage of a context (first element being the youngest, last element being the oldest),
    /// generate a bound analysis for a variable throughout the lineage
    fn bounds_for_var_in_family_tree(
        &self,
        file_mapping: &'_ BTreeMap<usize, String>,
        ordered_ctxs: Vec<ContextNode>,
        var_name: String,
        report_config: ReportConfig,
    ) -> VarBoundAnalysis {
        let mut inherited = None;
        ordered_ctxs
            .into_iter()
            .filter_map(|ctx| Some((ctx, ctx.var_by_name(self, &var_name)?)))
            .for_each(|(_ctx, cvar)| {
                let analysis = self.bounds_for_var_node(
                    &inherited,
                    file_mapping,
                    &var_name,
                    cvar,
                    report_config,
                    inherited.is_some(),
                );
                inherited = Some(analysis);
            });
        inherited.unwrap_or_default()
    }

    /// Analyzes the bounds for a variable up to the provided node
    fn bounds_for_var_node(
        &self,
        inherited: &Option<VarBoundAnalysis>,
        file_mapping: &'_ BTreeMap<usize, String>,
        var_name: &str,
        cvar: ContextVarNode,
        report_config: ReportConfig,
        is_subctx: bool,
    ) -> VarBoundAnalysis {
        let mut curr = cvar.first_version(self);

        let ctx = cvar.ctx(self);
        let (func_span, func_body_span) =
            if let Some(fn_call) = ctx.underlying(self).unwrap().fn_call {
                (
                    LocStrSpan::new(file_mapping, fn_call.underlying(self).unwrap().loc),
                    fn_call
                        .underlying(self)
                        .unwrap()
                        .body
                        .as_ref()
                        .map(|body| LocStrSpan::new(file_mapping, body.loc())),
                )
            } else if let Some(ext_fn_call) = ctx.underlying(self).unwrap().ext_fn_call {
                (
                    LocStrSpan::new(file_mapping, ext_fn_call.underlying(self).unwrap().loc),
                    ext_fn_call
                        .underlying(self)
                        .unwrap()
                        .body
                        .as_ref()
                        .map(|body| LocStrSpan::new(file_mapping, body.loc())),
                )
            } else {
                let fn_call = ctx.associated_fn(self).unwrap();
                (
                    LocStrSpan::new(file_mapping, fn_call.underlying(self).unwrap().loc),
                    fn_call
                        .underlying(self)
                        .unwrap()
                        .body
                        .as_ref()
                        .map(|body| LocStrSpan::new(file_mapping, body.loc())),
                )
            };

        let mut ba: VarBoundAnalysis = if let Some(inherited) = inherited {
            let mut new_ba = inherited.clone();
            let ctx_switch = CtxSwitch {
                ctx,
                func_span,
                func_body_span,
                killed_loc: ctx
                    .killed_loc(self)
                    .unwrap()
                    .map(|(loc, kind)| (LocStrSpan::new(file_mapping, loc), kind)),
            };

            new_ba.spanned_ctx_info.insert(ctx_switch);

            new_ba
        } else {
            VarBoundAnalysis {
                ctx,
                var_name: var_name.to_string(),
                var_display_name: cvar.display_name(self).unwrap(),
                func_span,
                var_def: (
                    LocStrSpan::new(file_mapping, curr.loc(self).unwrap()),
                    if !is_subctx {
                        curr.range(self).unwrap()
                    } else {
                        None
                    },
                ),
                bound_changes: vec![],
                report_config,
                storage: curr.underlying(self).unwrap().storage,
                ctx_killed: ctx
                    .killed_loc(self)
                    .unwrap()
                    .map(|(loc, kind)| (LocStrSpan::new(file_mapping, loc), kind)),
                ..Default::default()
            }
        };

        let (comparator, needs_curr) =
            if let Some(inherited) = curr.previous_or_inherited_version(self) {
                (inherited, true)
            } else {
                (curr, false)
            };

        if let Some(curr_range) = comparator.ref_range(self).unwrap() {
            let mut cr_min = curr_range.evaled_range_min(self).unwrap();
            let mut cr_max = curr_range.evaled_range_max(self).unwrap();
            let mut cr_excl = curr_range.range_exclusions();

            if needs_curr {
                if let Some(next_range) = curr.ref_range(self).unwrap() {
                    let nr_min = next_range.evaled_range_min(self).unwrap();
                    let nr_max = next_range.evaled_range_max(self).unwrap();
                    let nr_excl = &next_range.exclusions;

                    // check if there was a bound change
                    if report_config.show_all_lines
                        || nr_min != cr_min
                        || nr_max != cr_max
                        || nr_excl != &cr_excl
                    {
                        cr_min = nr_min;
                        cr_max = nr_max;
                        cr_excl = nr_excl.to_vec();
                        let new = (
                            LocStrSpan::new(file_mapping, curr.loc(self).unwrap()),
                            next_range.into_owned(),
                        );
                        if !ba.bound_changes.contains(&new) {
                            ba.bound_changes.push(new);
                        }
                    }
                }
            }

            while let Some(next) = curr.next_version(self) {
                if let Some(next_range) = next.ref_range(self).unwrap() {
                    let nr_min = next_range.evaled_range_min(self).unwrap();
                    let nr_max = next_range.evaled_range_max(self).unwrap();
                    let nr_excl = &next_range.exclusions;

                    // check if there was a bound change
                    if report_config.show_all_lines
                        || nr_min != cr_min
                        || nr_max != cr_max
                        || nr_excl != &cr_excl
                    {
                        cr_min = nr_min;
                        cr_max = nr_max;
                        cr_excl = nr_excl.to_vec();
                        let new = (
                            LocStrSpan::new(file_mapping, next.loc(self).unwrap()),
                            next_range.into_owned(),
                        );
                        if !ba.bound_changes.contains(&new) {
                            ba.bound_changes.push(new);
                        }
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
