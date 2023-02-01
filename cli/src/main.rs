use shared::context::*;
use shared::Edge;
use shared::analyzer::Search;
use clap::{Parser, ValueHint};
use std::fs;
use pyrometer::context::*;
use pyrometer::*;


#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH")]
    pub path: String,
}

fn main() {
    let args = Args::parse();
    let sol = fs::read_to_string(args.path).expect("Could not find file");
    let mut analyzer = Analyzer::default();
    let entry = analyzer.parse(&sol, 0).unwrap();
    let contexts = analyzer.search_children(entry, &crate::Edge::Context(ContextEdge::Context));
    for context in contexts.into_iter() {
        let config = ReportConfig {
            eval_bounds: true,
            simplify_bounds: false,
            show_tmps: false,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: true,
        };
        let ctx = ContextNode::from(context);

        let analysis = analyzer.bounds_for_all(ctx, config);
        analysis.print_reports((0, &sol), &analyzer);
    }
}
