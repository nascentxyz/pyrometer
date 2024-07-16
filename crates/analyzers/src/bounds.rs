use crate::{FunctionVarsBoundAnalysis, LocSpan, LocStrSpan, ReportConfig, VarBoundAnalysis};

use graph::{
    elem::Elem,
    nodes::{Concrete, ContextNode, KilledKind},
    range_string::ToRangeString,
    GraphBackend, Range, RangeEval, SolcRange,
};
use shared::{RangeArena, StorageLocation};

use ariadne::{Color, Fmt, Label, Span};
use std::collections::{BTreeMap, BTreeSet};

pub static MIN_COLOR: Color = Color::Fixed(111);
pub static MAX_COLOR: Color = Color::Fixed(106);

pub fn killed_kind_color(kind: &KilledKind) -> Color {
    match kind {
        KilledKind::Ended => Color::Green,
        KilledKind::Unreachable => Color::Rgb(255, 121, 0),
        _ => Color::Red,
    }
}

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
    pub fn from_bound_analysis(
        ba: VarBoundAnalysis,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Self {
        let mut analyses: BTreeMap<usize, BTreeSet<StrippedAnalysisItem>> = Default::default();
        if let Some(init) = ba.init_item(analyzer, arena) {
            let source: usize = *LocSpan(init.loc.1).source();
            let mut set = BTreeSet::new();
            set.insert(init.into());
            analyses.insert(source, set);
        }
        ba.bound_changes.iter().for_each(|bound_change| {
            let (parts, unsat) = range_parts(analyzer, arena, &ba.report_config, &bound_change.1);
            let item = StrippedAnalysisItem {
                init: false,
                name: ba.var_display_name.clone(),
                loc: LocSpan(bound_change.0 .1),
                order: (bound_change.0.end() - bound_change.0.start()) as i32, //i as i32,
                // storage: ba.storage.clone(),
                ctx: ba.ctx,
                ctx_conditionals: ba.conditionals(analyzer, arena),
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
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Self {
        let mut analyses = Self::default();
        fvba.vars_by_ctx.iter().for_each(|(_ctx, bas)| {
            bas.iter().for_each(|ba| {
                analyses.extend(Self::from_bound_analysis(ba.clone(), analyzer, arena));
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

impl From<AnalysisItem> for Label<LocStrSpan> {
    fn from(val: AnalysisItem) -> Self {
        let (color, order, priority) = if val.init {
            (Color::Magenta, val.order, -1)
        } else {
            (
                match val.storage {
                    Some(StorageLocation::Memory(..)) => Color::Blue,
                    Some(StorageLocation::Storage(..)) => Color::Green,
                    Some(StorageLocation::Calldata(..)) => Color::White,
                    Some(StorageLocation::Block(..)) => Color::Magenta,
                    Some(StorageLocation::Msg(..)) => Color::Cyan,
                    None => Color::Cyan,
                },
                val.order,
                0,
            )
        };

        Label::new(val.loc)
            .with_message(format!(
                "{}\"{}\"{}{}",
                match val.storage {
                    Some(StorageLocation::Memory(..)) => "Memory var ",
                    Some(StorageLocation::Storage(..)) => "Storage var ",
                    Some(StorageLocation::Calldata(..)) => "Calldata var ",
                    Some(StorageLocation::Block(..)) => "Block var ",
                    Some(StorageLocation::Msg(..)) => "Msg var ",
                    None => "",
                },
                val.name,
                val.parts
                    .into_iter()
                    .map(|part| part.to_cli_string())
                    .collect::<Vec<_>>()
                    .join(" "),
                if val.unsat {
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

/// Creates an Vec<[RangePart]> from a range based on the current [ReportConfig]
pub fn range_parts(
    analyzer: &impl GraphBackend,
    arena: &mut RangeArena<Elem<Concrete>>,
    report_config: &ReportConfig,
    range: &SolcRange,
) -> (Vec<RangePart>, bool) {
    let mut parts = vec![];
    let min = if report_config.eval_bounds {
        range
            .evaled_range_min(analyzer, arena)
            .unwrap()
            .to_range_string(false, analyzer, arena)
            .s
    } else if report_config.simplify_bounds {
        range
            .simplified_range_min(analyzer, arena)
            .unwrap()
            .to_range_string(false, analyzer, arena)
            .s
    } else {
        range.range_min().to_range_string(false, analyzer, arena).s
    };
    let max = if report_config.eval_bounds {
        range
            .evaled_range_max(analyzer, arena)
            .unwrap()
            .to_range_string(true, analyzer, arena)
            .s
    } else if report_config.simplify_bounds {
        range
            .simplified_range_max(analyzer, arena)
            .unwrap()
            .to_range_string(true, analyzer, arena)
            .s
    } else {
        range.range_max().to_range_string(true, analyzer, arena).s
    };

    if min == max {
        parts.push(RangePart::Equal(min));
    } else {
        parts.push(RangePart::Inclusion(min, max));
    }

    let range_excl = range.range_exclusions();
    if !range_excl.is_empty() {
        parts.push(RangePart::Exclusion({
            let mut excls = range_excl
                .iter()
                .map(|range| {
                    let min = range.to_range_string(false, analyzer, arena).s;
                    let max = range.to_range_string(true, analyzer, arena).s;
                    if min == max {
                        RangePart::Equal(min)
                    } else {
                        RangePart::Inclusion(min, max)
                    }
                })
                .collect::<Vec<_>>();
            excls.dedup();
            excls
        }));
    }
    let unsat = range.unsat(analyzer, arena);
    (parts, unsat)
}
