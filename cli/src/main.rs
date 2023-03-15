use crate::analyzers::ReportConfig;
use ariadne::sources;
use clap::{ArgAction, Parser, ValueHint};
use pyrometer::context::queries::storage_write::StorageRangeQuery;
use pyrometer::{
    context::{
        analyzers::{bounds::FunctionVarsBoundAnalyzer, ReportDisplay},
        queries::storage_write::AccessStorageWriteQuery,
        *,
    },
    Analyzer,
};
use shared::nodes::Concrete;
use shared::range::SolcRange;
use shared::{
    analyzer::{GraphLike, Search},
    nodes::ContractNode,
};
use std::collections::{BTreeMap, HashMap};
use std::io::Write;
use std::process::Command;

use shared::nodes::FunctionNode;

use shared::Edge;
use std::env::temp_dir;
use std::fs;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH")]
    pub path: String,
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
    pub write_query: Vec<String>,
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
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        1 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: false,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        2 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
        },
        3 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
        },
        4 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: true,
        },
        _ => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: false,
            show_tmps: true,
            show_consts: true,
            show_subctxs: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: true,
        },
    };

    let sol = fs::read_to_string(args.path.clone()).expect("Could not find file");

    let mut analyzer = Analyzer::default();
    let t0 = std::time::Instant::now();
    let (maybe_entry, mut all_sources) = analyzer.parse(&sol);
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
                        .starts_with(analyze_for)
                }) {
                    if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&analyzer) {
                        let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            } else if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&analyzer) {
                let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
                analysis.print_reports(&mut source_map, &analyzer);
            }
        }
    } else {
        // println!("specified contracts: {:?}", all_contracts);
        all_contracts
            .iter()
            .filter(|contract| args.contracts.contains(&contract.name(&analyzer)))
            .for_each(|contract| {
                let funcs = contract.funcs(&analyzer);
                for func in funcs.into_iter() {
                    if !args.funcs.is_empty() {
                        if args.funcs.contains(&func.name(&analyzer)) {
                            let ctx = func.body_ctx(&analyzer);
                            let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
                            analysis.print_reports(&mut source_map, &analyzer);
                        }
                    } else {
                        let ctx = func.body_ctx(&analyzer);
                        let analysis = analyzer.bounds_for_all(&file_mapping, ctx, config);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            });
    }

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
            SolcRange {
                min: Concrete::Bool(true).into(),
                max: Concrete::Bool(true).into(),
                exclusions: vec![],
            },
        ) {
            report.print_reports(&mut source_map, &analyzer);
        }
        println!();
    });

    // println!("parse time: {:?}ms", parse_time);
    // println!("analyzer time: {:?}ms", t1.elapsed().as_millis());
    // println!("total time: {:?}ms", t0.elapsed().as_millis());

    if args.open_dot {
        let mut dir = temp_dir();
        let file_name = "dot.dot";
        dir.push(file_name);

        let mut file = fs::File::create(dir.clone()).unwrap();
        file.write_all(analyzer.dot_str().as_bytes()).unwrap();
        Command::new("dot")
            .arg("-Tjpeg")
            .arg(dir)
            .arg("-o")
            .arg("dot.jpeg")
            .output()
            .expect("failed to execute process");
        Command::new("open")
            .arg("dot.jpeg")
            .output()
            .expect("failed to execute process");
    }
}
