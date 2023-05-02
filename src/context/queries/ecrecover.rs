use crate::analyzers::{VarBoundAnalyzer, *};
use shared::context::CallFork;

use shared::{analyzer::*, NodeIdx};

use ariadne::{Cache, Color, Config, Label, Report, ReportKind};

#[derive(Debug, Clone)]
pub struct TaintReport {
    pub msgs: Vec<String>,
}

impl TaintReport {
    pub fn new(msgs: Vec<String>) -> Self {
        Self { msgs }
    }
}

impl ReportDisplay for TaintReport {
    fn report_kind(&self) -> ReportKind {
        ReportKind::Custom("Taint Analysis", Color::Green)
    }
    fn msg(&self, _analyzer: &impl GraphLike) -> String {
        self.msgs.join(";\n")
    }

    fn labels(&self, _analyzer: &impl GraphLike) -> Vec<Label<LocStrSpan>> {
        vec![]
    }

    fn reports(&self, analyzer: &impl GraphLike) -> Vec<Report<LocStrSpan>> {
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

    fn print_reports(&self, src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        for report in reports.iter() {
            report.print(&mut *src).unwrap();
        }
    }

    fn eprint_reports(&self, mut src: &mut impl Cache<String>, analyzer: &impl GraphLike) {
        let reports = &self.reports(analyzer);
        reports.iter().for_each(|report| {
            report.eprint(&mut src).unwrap();
        });
    }
}

impl<T> TaintQuery for T where T: VarBoundAnalyzer + Search + AnalyzerLike + Sized {}
pub trait TaintQuery: VarBoundAnalyzer + Search + AnalyzerLike + Sized {
    #[allow(clippy::too_many_arguments)]
    fn taint_query(&self, _entry: NodeIdx, _contract_name: String) {
        // let contract = self
        //     .search_children(entry, &crate::Edge::Contract)
        //     .into_iter()
        //     .filter(|contract| ContractNode::from(*contract).name(self).unwrap() == contract_name)
        //     .take(1)
        //     .next()
        //     .expect("No contract with provided name");

        // let con_node = ContractNode::from(contract);
        // for func in con_node
        //     .funcs(self)
        //     .iter() {
        //         let ctx = func.body_ctx(self);
        //         let ext_ret_assignments = ctx.vars_assigned_from_ext_fn_ret(self);
        //         println!("\n\nHERE ext ret assignments: {:#?}\n\n", ext_ret_assignments);
        //         let children = &ctx.underlying(self).unwrap().children;
        //         children.iter().for_each(|child| self.recurse_children(*child));
        // }
    }

    fn recurse_children(&self, _child: CallFork) {
        // let node = child.either();
        // let ext_ret_assignments = node.vars_assigned_from_ext_fn_ret(self);
        // println!("\n\next ret assignments: {:#?}\n\n", ext_ret_assignments);
        // let called_fns = node.called_functions(self).unwrap();
        // called_fns.iter().filter(|fn_node| {
        //     fn_node.name(self).unwrap() == "ecrecover"
        // }).for_each(|fn_node| println!("CALLED ECRECOVER"));
        // let children = &node.underlying(self).unwrap().children;
        // children.iter().for_each(|child| self.recurse_children(*child));
    }
}
