pub mod bounds;

use graph::{GraphBackend, AnalyzerBackend};
use ariadne::{Cache, Label, Report, ReportKind, Span};
use shared::Search;
use solang_parser::pt::Loc;
use std::collections::BTreeMap;

mod func_analyzer;
pub use func_analyzer::*;
mod var_analyzer;
pub use var_analyzer::*;

pub trait ContextAnalyzer:
    AnalyzerBackend + Search + VarBoundAnalyzer + FunctionVarsBoundAnalyzer
{
}
impl<T> ContextAnalyzer for T where
    T: AnalyzerBackend + Search + VarBoundAnalyzer + FunctionVarsBoundAnalyzer
{
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct LocSpan(pub Loc);

impl Default for LocSpan {
    fn default() -> Self {
        LocSpan(Loc::Implicit)
    }
}

impl Span for LocSpan {
    type SourceId = usize;
    fn source(&self) -> &Self::SourceId {
        match self.0 {
            Loc::File(ref f, _, _) => f,
            Loc::Implicit => &0,
            _ => todo!("handle non file loc"),
        }
    }

    fn start(&self) -> usize {
        match self.0 {
            Loc::File(_, start, _) => start,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }

    fn end(&self) -> usize {
        match self.0 {
            Loc::File(_, _, end) => end,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct LocStrSpan(pub String, pub Loc);

impl Default for LocStrSpan {
    fn default() -> Self {
        LocStrSpan("".to_string(), Loc::Implicit)
    }
}

impl LocStrSpan {
    pub fn new(file_mapping: &BTreeMap<usize, String>, loc: Loc) -> Self {
        let source = match loc {
            Loc::File(ref f, _, _) => f,
            Loc::Implicit => &0,
            _ => todo!("handle non file loc"),
        };
        LocStrSpan(
            file_mapping
                .get(source)
                .expect("No file for num")
                .to_string(),
            loc,
        )
    }
}

impl Span for LocStrSpan {
    type SourceId = String;
    fn source(&self) -> &Self::SourceId {
        &self.0
    }

    fn start(&self) -> usize {
        match self.1 {
            Loc::File(_, start, _) => start,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }

    fn end(&self) -> usize {
        match self.1 {
            Loc::File(_, _, end) => end,
            Loc::Implicit => 0,
            _ => todo!("handle non file loc"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct ReportConfig {
    pub eval_bounds: bool,
    pub simplify_bounds: bool,
    pub show_tmps: bool,
    pub show_consts: bool,
    pub show_symbolics: bool,
    pub show_initial_bounds: bool,
    pub show_all_lines: bool,
    pub show_reverts: bool,
    pub show_unreachables: bool,
    pub show_nonreverts: bool,
}

impl ReportConfig {
    pub fn new(
        eval_bounds: bool,
        simplify_bounds: bool,
        show_tmps: bool,
        show_consts: bool,
        show_symbolics: bool,
        show_initial_bounds: bool,
        show_all_lines: bool,
        show_reverts: bool,
        show_unreachables: bool,
        show_nonreverts: bool,
    ) -> Self {
        Self {
            eval_bounds,
            simplify_bounds,
            show_tmps,
            show_consts,
            show_symbolics,
            show_initial_bounds,
            show_all_lines,
            show_reverts,
            show_unreachables,
            show_nonreverts,
        }
    }
}

impl Default for ReportConfig {
    fn default() -> Self {
        Self {
            eval_bounds: true,
            simplify_bounds: false,
            show_tmps: false,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: false,
            show_all_lines: false,
            show_reverts: false,
            show_unreachables: false,
            show_nonreverts: true,
        }
    }
}

pub trait ReportDisplay {
    fn report_kind(&self) -> ReportKind;
    fn msg(&self, analyzer: &impl GraphBackend) -> String;
    fn labels(&self, analyzer: &impl GraphBackend) -> Vec<Label<LocStrSpan>>;
    fn reports(&self, analyzer: &impl GraphBackend) -> Vec<Report<LocStrSpan>>;
    fn print_reports(&self, src: &mut impl Cache<String>, analyzer: &impl GraphBackend);
    fn eprint_reports(&self, src: &mut impl Cache<String>, analyzer: &impl GraphBackend);
}
