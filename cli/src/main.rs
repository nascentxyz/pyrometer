use crate::analyzers::ReportConfig;
use ariadne::sources;
use clap::{ArgAction, Parser, ValueHint};
use pyrometer::context::analyzers::FunctionVarsBoundAnalyzer;
use pyrometer::context::queries::storage_write::StorageRangeQuery;

use pyrometer::{
    context::{
        analyzers::ReportDisplay, queries::ecrecover::TaintQuery,
        queries::storage_write::AccessStorageWriteQuery, *,
    },
    Analyzer,
};
use shared::nodes::Concrete;
use shared::nodes::FunctionNode;
use shared::range::SolcRange;
use shared::Edge;
use shared::{
    analyzer::{GraphLike, Search},
    nodes::ContractNode,
};
use tracing_subscriber::prelude::*;

use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

use std::env::{self};
use std::fs;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH")]
    pub path: String,
    #[clap(long, short)]
    pub remappings: Option<String>,
    #[clap(long, short)]
    pub contracts: Vec<String>,
    #[clap(long, short)]
    pub funcs: Vec<String>,
    #[clap(long, short, verbatim_doc_comment, action = ArgAction::Count)]
    pub verbosity: u8,
    #[clap(long, short, default_value = "false")]
    pub dot: bool,
    #[clap(long, short, default_value = "false")]
    pub open_dot: bool,
    #[clap(long, short)]
    pub eval: Option<bool>,
    #[clap(long, short)]
    pub show_inits: Option<bool>,
    #[clap(long, short)]
    pub access_query: Vec<String>,
    #[clap(long, short)]
    pub query: Vec<String>,
    #[clap(long, short)]
    pub write_query: Vec<String>,
}

pub fn subscriber() {
    tracing_subscriber::Registry::default()
        .with(tracing_subscriber::filter::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .init()
}

fn main() {
    subscriber();
    let args = Args::parse();
    let path_str = args.path.to_string();
    let verbosity = args.verbosity;
    let config = match verbosity {
        0 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: false,
            show_symbolics: false,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        1 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        2 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        3 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
        },
        4 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
        },
        _ => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: true,
        },
    };

    let sol = fs::read_to_string(args.path.clone()).expect("Could not find file");

    let mut analyzer = Analyzer {
        root: env::current_dir().unwrap(),
        ..Default::default()
    };
    if args.remappings.is_some() {
        let remappings = args.remappings.unwrap();
        analyzer.set_remappings_and_root(remappings);
    }
    let t0 = std::time::Instant::now();
    let (maybe_entry, mut all_sources) =
        analyzer.parse(&sol, &PathBuf::from(args.path.clone()), true);
    let _parse_time = t0.elapsed().as_millis();
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

    analyzer.print_errors(&file_mapping, &mut source_map);

    if args.dot {
        println!("{}", analyzer.dot_str_no_tmps());
    }

    let all_contracts = analyzer
        .search_children(entry, &Edge::Contract)
        .into_iter()
        .map(ContractNode::from)
        .collect::<Vec<_>>();
    let _t1 = std::time::Instant::now();
    if args.contracts.is_empty() {
        let funcs = analyzer.search_children(entry, &Edge::Func);
        for func in funcs.into_iter() {
            if !args.funcs.is_empty() {
                if args.funcs.iter().any(|analyze_for| {
                    FunctionNode::from(func)
                        .name(&analyzer)
                        .unwrap()
                        .starts_with(analyze_for)
                }) {
                    if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&analyzer) {
                        // println!("{:#?}", analyzer.call_trace(ctx));
                        let analysis = analyzer
                            .bounds_for_all(&file_mapping, ctx, config)
                            .as_cli_compat(&file_mapping);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            } else if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&analyzer) {
                // analyzer
                //     .call_trace(ctx)
                //     .unwrap()
                //     .into_iter()
                //     .for_each(|i| println!("{i}\n"));
                let analysis = analyzer
                    .bounds_for_all(&file_mapping, ctx, config)
                    .as_cli_compat(&file_mapping);
                analysis.print_reports(&mut source_map, &analyzer);
            }
        }
    } else {
        // println!("specified contracts: {:?}", all_contracts);
        all_contracts
            .iter()
            .filter(|contract| args.contracts.contains(&contract.name(&analyzer).unwrap()))
            .for_each(|contract| {
                let funcs = contract.funcs(&analyzer);
                for func in funcs.into_iter() {
                    if !args.funcs.is_empty() {
                        if args.funcs.contains(&func.name(&analyzer).unwrap()) {
                            let ctx = func.body_ctx(&analyzer);
                            let analysis = analyzer
                                .bounds_for_all(&file_mapping, ctx, config)
                                .as_cli_compat(&file_mapping);
                            analysis.print_reports(&mut source_map, &analyzer);
                        }
                    } else {
                        let ctx = func.body_ctx(&analyzer);
                        let analysis = analyzer
                            .bounds_for_all(&file_mapping, ctx, config)
                            .as_cli_compat(&file_mapping);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            });
    }

    args.query.iter().for_each(|query| {
        analyzer.taint_query(entry, query.to_string());
        // .print_reports(&mut source_map, &analyzer);
        println!();
    });

    args.access_query.iter().for_each(|query| {
        let split: Vec<&str> = query.split('.').collect();
        analyzer
            .access_query(
                entry,
                &file_mapping,
                config,
                split[0].to_string(),
                split[1].to_string(),
            )
            .print_reports(&mut source_map, &analyzer);
        println!();
    });

    args.write_query.iter().for_each(|query| {
        let split: Vec<&str> = query.split('.').collect();
        // println!("{:?}", split);
        if let Some(report) = analyzer.func_query(
            entry,
            &file_mapping,
            config,
            split[0].to_string(),
            split[1].to_string(),
            split[2].to_string(),
            SolcRange::new(
                Concrete::Bool(true).into(),
                Concrete::Bool(true).into(),
                vec![],
            ),
        ) {
            report.print_reports(&mut source_map, &analyzer);
        }
        println!();
    });

    if args.open_dot {
        analyzer.open_dot()
    }
}
