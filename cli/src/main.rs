use ariadne::sources;
use clap::{ArgAction, Parser, ValueHint};
use pyrometer::context::*;
use pyrometer::*;
use shared::analyzer::GraphLike;
use shared::analyzer::Search;
use std::collections::BTreeMap;
use std::collections::HashMap;

use shared::nodes::FunctionNode;

use shared::Edge;
use std::fs;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH")]
    pub path: String,
    #[clap(long, short)]
    pub funcs: Vec<String>,
    #[clap(long, short, verbatim_doc_comment, action = ArgAction::Count)]
    pub verbosity: u8,
    #[clap(long, short, default_value = "false")]
    pub dot: bool,
    #[clap(long, short)]
    pub eval: Option<bool>,
}

fn main() {
    let args = Args::parse();
    let path_str = args.path.to_string();
    let verbosity = args.verbosity;
    let config = match verbosity {
        0 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: false,
            show_subctxs: true,
            show_initial_bounds: false,
        },
        1 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: false,
            show_subctxs: true,
            show_initial_bounds: true,
        },
        2 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: true,
        },
        _ => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: true,
        },
    };

    let sol = fs::read_to_string(args.path.clone()).expect("Could not find file");

    let mut analyzer = Analyzer::default();
    let (maybe_entry, mut all_sources) = analyzer.parse(&sol);
    all_sources.push((maybe_entry, args.path, sol, 0));
    let entry = maybe_entry.unwrap();

    let mut file_mapping: BTreeMap<_, _> = vec![(0usize, path_str)].into_iter().collect();
    file_mapping.extend(
        all_sources
            .iter()
            .map(|(_entry, name, _src, num)| (*num, name.clone()))
            .collect::<BTreeMap<_, _>>(),
    );

    let mut source_map = sources(
        all_sources
            .iter()
            .map(|(_entry, name, src, _num)| (name.clone(), src))
            .collect::<HashMap<_, _>>(),
    );

    if args.dot {
        println!("{}", analyzer.dot_str_no_tmps());
    }

    let funcs = analyzer.search_children(entry, &crate::Edge::Func);
    for func in funcs.into_iter() {
        if !args.funcs.is_empty() {
            if args
                .funcs
                .contains(&FunctionNode::from(func).name(&analyzer))
            {
                let ctx = FunctionNode::from(func).body_ctx(&analyzer);
                let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
                analysis.print_reports(&mut source_map, &analyzer);
            }
        } else {
            let ctx = FunctionNode::from(func).body_ctx(&analyzer);
            let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
            analysis.print_reports(&mut source_map, &analyzer);
        }
    }

    // if let Some(write) = analyzer.func_query(
    //     entry,
    //     &file_mapping,
    //     config,
    //     "Storage".to_string(),
    //     "b5".to_string(),
    //     "c".to_string(),
    //     SolcRange::from(Concrete::Uint(256, 16.into())).unwrap(),
    // ) {
    //     write.print_reports((path_str.clone(), &sol), &analyzer);
    // }
}
