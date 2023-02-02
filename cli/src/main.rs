use shared::nodes::Concrete;
use shared::range::SolcRange;
use shared::nodes::FunctionNode;
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
    let path_str = args.path.clone().to_string();
    let sol = fs::read_to_string(args.path).expect("Could not find file");
    let config = ReportConfig {
        eval_bounds: true,
        simplify_bounds: true,
        show_tmps: true,
        show_consts: true,
        show_subctxs: true,
        show_initial_bounds: true,
    };

    let mut analyzer = Analyzer::default();
    let entry = analyzer.parse(&sol, 0).unwrap();
    let file_mapping = vec![(0usize, path_str.clone())].into_iter().collect();
    let funcs = analyzer.search_children(entry, &crate::Edge::Func);
    for func in funcs.into_iter() {
        let ctx = FunctionNode::from(func).body_ctx(&analyzer);
        println!("ctx: {}", ctx.path(&analyzer));
        

        // let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
        // analysis.print_reports((path_str.clone(), &sol), &analyzer);

        // let analysis = analyzer.bounds_for_var(None, &file_mapping, ctx, "d".to_string(), config, false);
        // println!("here {:#?}", analysis);
        // analysis[0].1.print_reports((path_str.clone(), &sol), &analyzer)
    }

    if let Some(write) = analyzer.func_query(
        entry,
        &file_mapping,
        config,
        "Baz".to_string(),
        "baz".to_string(),
        "state1".to_string(),
        SolcRange::from(Concrete::Bool(true)).expect("here")
    ) {
        write.print_reports((path_str.clone(), &sol), &analyzer);
    }

    if let Some(write) = analyzer.func_query(
        entry,
        &file_mapping,
        config,
        "Baz".to_string(),
        "baz".to_string(),
        "state2".to_string(),
        SolcRange::from(Concrete::Bool(true)).expect("here")
    ) {
        write.print_reports((path_str.clone(), &sol), &analyzer);
    }

    if let Some(write) = analyzer.func_query(
        entry,
        &file_mapping,
        config,
        "Baz".to_string(),
        "baz".to_string(),
        "state3".to_string(),
        SolcRange::from(Concrete::Bool(true)).expect("here")
    ) {
        write.print_reports((path_str.clone(), &sol), &analyzer);
    }

    if let Some(write) = analyzer.func_query(
        entry,
        &file_mapping,
        config,
        "Baz".to_string(),
        "baz".to_string(),
        "state4".to_string(),
        SolcRange::from(Concrete::Bool(true)).expect("here")
    ) {
        write.print_reports((path_str.clone(), &sol), &analyzer);
    }

    if let Some(write) = analyzer.func_query(
        entry,
        &file_mapping,
        config,
        "Baz".to_string(),
        "baz".to_string(),
        "state5".to_string(),
        SolcRange::from(Concrete::Bool(true)).expect("here")
    ) {
        write.print_reports((path_str.clone(), &sol), &analyzer);
    }
}
