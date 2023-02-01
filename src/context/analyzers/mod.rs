pub mod array;
pub use array::*;
pub mod bounds;
pub use bounds::*;

use shared::analyzer::Search;
use crate::{AnalyzerLike};
use ariadne::{Label, Report, ReportKind, Span};
use solang_parser::pt::Loc;

pub trait ContextAnalyzer:
    AnalyzerLike + Search + BoundAnalyzer + FunctionVarsBoundAnalyzer + ArrayAccessAnalyzer
{
}
impl<T> ContextAnalyzer for T where
    T: AnalyzerLike + Search + BoundAnalyzer + FunctionVarsBoundAnalyzer + ArrayAccessAnalyzer
{
}

#[derive(Debug, Copy, Clone)]
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

#[derive(Debug, Clone, Copy)]
pub struct ReportConfig {
    pub eval_bounds: bool,
    pub simplify_bounds: bool,
    pub show_tmps: bool,
    pub show_consts: bool,
    pub show_subctxs: bool,
    pub show_initial_bounds: bool,
}

impl ReportConfig {
    pub fn new(
        eval_bounds: bool,
        simplify_bounds: bool,
        show_tmps: bool,
        show_consts: bool,
        show_subctxs: bool,
        show_initial_bounds: bool,
    ) -> Self {
        Self {
            eval_bounds,
            simplify_bounds,
            show_tmps,
            show_consts,
            show_subctxs,
            show_initial_bounds,
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
            show_subctxs: true,
            show_initial_bounds: true,
        }
    }
}

pub trait ReportDisplay {
    fn report_kind(&self) -> ReportKind;
    fn msg(&self, analyzer: &(impl AnalyzerLike + Search)) -> String;
    fn labels(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Label<LocSpan>>;
    fn reports(&self, analyzer: &(impl AnalyzerLike + Search)) -> Vec<Report<LocSpan>>;
    fn print_reports(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search));
    fn eprint_reports(&self, src: (usize, &str), analyzer: &(impl AnalyzerLike + Search));
}
