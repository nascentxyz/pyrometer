use crate::analyzers::ReportConfig;
use ariadne::sources;
use clap::{ArgAction, Parser, ValueHint};
use pyrometer::context::analyzers::FunctionVarsBoundAnalyzer;
use pyrometer::Root;
use pyrometer::{
    context::{analyzers::ReportDisplay, *},
    Analyzer, SourcePath,
};

use shared::nodes::FunctionNode;

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
    /// The path to the solidity file to process
    #[clap(value_hint = ValueHint::FilePath, value_name = "PATH")]
    pub path: String,
    /// The path to the `remappings.txt` as per the output of `forge remappings`
    #[clap(long, short)]
    pub remappings: Option<String>,
    /// Limit the output to just contracts that start with the name passed. i.e. `--contracts "MyCon"` woudl match "MyContract", "MyCon2", .. etc.
    ///
    /// Can be passed multiple times, i.e. `--contract "MyCon" --contract "MyOtherContract"`
    #[clap(long, short)]
    pub contracts: Vec<String>,
    /// Limit the output to just functions that start with the name passed. i.e. `--funcs "myFunc"` would match "myFunction", "myFunc2", .. etc.
    ///
    /// Can be passed multiple times, i.e. `--funcs "myFunc" --funcs "myOtherFunc"`
    #[clap(long, short)]
    pub funcs: Vec<String>,
    /// Verbosity of the bounds analysis
    ///
    /// Pass multiple times to increase the verbosity (e.g. -v, -vv, -vvv).
    ///
    /// Verbosity levels:
    ///
    ///   0: Print return value changes
    ///   1: Print storage variable changes, input variable changes, and return value changes
    ///   2: Print all previous values as well as temporary values
    ///   3: Print all previous values as well as initial values
    ///   4: Print all previous values as well as constants
    ///   5: Print all previous values for all successful branches and reverting branches
    ///   6: Print all previous values for all successful branches, reverting branches, and unreachable branches
    #[clap(long, short, verbatim_doc_comment, action = ArgAction::Count)]
    pub verbosity: u8,
    /// Whether to print out a dot string of the analyzed contracts
    #[clap(long, short, default_value = "false")]
    pub dot: bool,
    /// Whether to generate and open a dot visualization of the analyzed contracts
    #[clap(long, short, default_value = "false")]
    pub open_dot: bool,
    /// Whether to evaluate variables down to their intervals or to keep them symbolic/relational to other variables
    #[clap(long, short)]
    pub eval: Option<bool>,
    /// Whether to simplify expressions down to variables down to their intervals or to keep them symbolic/relational to other variables
    #[clap(long, short)]
    pub simplify: Option<bool>,
    /// Whether to show initial values in the bounds analysis output
    #[clap(long)]
    pub show_inits: Option<bool>,
    /// Show reverting paths
    #[clap(long)]
    pub show_reverts: Option<bool>,
    /// Show unreachable paths
    #[clap(long)]
    pub show_unreachables: Option<bool>,
    /// Show non-revert paths
    #[clap(long)]
    pub show_nonreverts: Option<bool>,
    // #[clap(long, short)]
    // pub access_query: Vec<String>,
    // #[clap(long, short)]
    // pub query: Vec<String>,
    // #[clap(long, short)]
    // pub write_query: Vec<String>,
    /// A debugging command to prevent bound analysis printing. Useful for debugging parse errors during development. Only prints out parse errors
    /// then ends the program
    #[clap(long)]
    pub debug: bool,
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
    let verbosity = args.verbosity;
    let config = match verbosity {
        0 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: false,
            show_consts: false,
            show_symbolics: false,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(false),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        1 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: false,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(false),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        2 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(false),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(false),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        3 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: false,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(false),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        4 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(false),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        5 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(true),
            show_unreachables: args.show_unreachables.unwrap_or(false),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        6 => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: false,
            show_reverts: args.show_reverts.unwrap_or(true),
            show_unreachables: args.show_unreachables.unwrap_or(true),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
        _ => ReportConfig {
            eval_bounds: args.eval.unwrap_or(true),
            simplify_bounds: args.simplify.unwrap_or(false),
            show_tmps: true,
            show_consts: true,
            show_symbolics: true,
            show_initial_bounds: args.show_inits.unwrap_or(true),
            show_all_lines: true,
            show_reverts: args.show_reverts.unwrap_or(true),
            show_unreachables: args.show_unreachables.unwrap_or(true),
            show_nonreverts: args.show_nonreverts.unwrap_or(true),
        },
    };
    let root = Root::RemappingsDirectory(env::current_dir().unwrap());
    let mut analyzer = Analyzer {
        root: root,
        ..Default::default()
    };

    let (current_path, sol) = if args.path.ends_with(".sol") {
        let sol = fs::read_to_string(args.path.clone()).expect("Could not find file");
        // Remappings file only required for Solidity files
        if args.remappings.is_some() {
            let remappings = args.remappings.unwrap();
            analyzer.set_remappings_and_root(remappings);
        }

        (
            SourcePath::SolidityFile(PathBuf::from(args.path.clone())),
            sol,
        )
    } else if args.path.ends_with(".json") {
        let json_path_buf = PathBuf::from(args.path.clone());
        analyzer.update_with_solc_json(&json_path_buf);
        let (current_path, sol, _, _) = analyzer.sources.iter().next().unwrap().clone();
        (current_path, sol)
    } else {
        panic!("Unsupported file type")
    };

    let t0 = std::time::Instant::now();
    let maybe_entry = analyzer.parse(&sol, &current_path, true);
    let parse_time = t0.elapsed().as_millis();

    println!("DONE ANALYZING IN: {parse_time}ms. Writing to cli...");

    // use self.sources to fill a BTreeMap with the file_no and SourcePath.path_to_solidity_file
    let mut file_mapping: BTreeMap<usize, String> = BTreeMap::new();
    let mut src_map: HashMap<String, String> = HashMap::new();
    for (source_path, sol, o_file_no, _o_entry) in analyzer.sources.iter() {
        if let Some(file_no) = o_file_no {
            file_mapping.insert(
                *file_no,
                source_path.path_to_solidity_source().display().to_string(),
            );
        }
        src_map.insert(
            source_path.path_to_solidity_source().display().to_string(),
            sol.to_string(),
        );
    }
    let mut source_map = sources(src_map);

    // all_sources.push((maybe_entry, args.path, sol, 0));
    let entry = maybe_entry.unwrap();

    analyzer.print_errors(&file_mapping, &mut source_map);

    if args.open_dot {
        analyzer.open_dot()
    }

    if args.dot {
        println!("{}", analyzer.dot_str_no_tmps());
    }

    if args.debug {
        return;
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
                    if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&mut analyzer) {
                        let analysis = analyzer
                            .bounds_for_all(&file_mapping, ctx, config)
                            .as_cli_compat(&file_mapping);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            } else if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&mut analyzer) {
                let analysis = analyzer
                    .bounds_for_all(&file_mapping, ctx, config)
                    .as_cli_compat(&file_mapping);
                analysis.print_reports(&mut source_map, &analyzer);
            }
        }
    } else {
        all_contracts
            .iter()
            .filter(|contract| {
                let name: String = contract.name(&analyzer).unwrap();
                args.contracts.contains(&name)
            })
            .collect::<Vec<_>>()
            .iter()
            .for_each(|contract| {
                let funcs = contract.funcs(&analyzer);
                for func in funcs.into_iter() {
                    if !args.funcs.is_empty() {
                        if args.funcs.contains(&func.name(&analyzer).unwrap()) {
                            let ctx = func.body_ctx(&mut analyzer);
                            let analysis = analyzer
                                .bounds_for_all(&file_mapping, ctx, config)
                                .as_cli_compat(&file_mapping);
                            analysis.print_reports(&mut source_map, &analyzer);
                        }
                    } else {
                        let ctx = func.body_ctx(&mut analyzer);
                        let analysis = analyzer
                            .bounds_for_all(&file_mapping, ctx, config)
                            .as_cli_compat(&file_mapping);
                        analysis.print_reports(&mut source_map, &analyzer);
                    }
                }
            });
    }

    // args.query.iter().for_each(|query| {
    //     analyzer.taint_query(entry, query.to_string());
    //     println!();
    // });

    // args.access_query.iter().for_each(|query| {
    //     let split: Vec<&str> = query.split('.').collect();
    //     analyzer
    //         .access_query(
    //             entry,
    //             &file_mapping,
    //             config,
    //             split[0].to_string(),
    //             split[1].to_string(),
    //         )
    //         .print_reports(&mut source_map, &analyzer);
    //     println!();
    // });

    // args.write_query.iter().for_each(|query| {
    //     let split: Vec<&str> = query.split('.').collect();
    //     if let Some(report) = analyzer.func_query(
    //         entry,
    //         &file_mapping,
    //         config,
    //         split[0].to_string(),
    //         split[1].to_string(),
    //         split[2].to_string(),
    //         SolcRange::new(
    //             Concrete::Bool(true).into(),
    //             Concrete::Bool(true).into(),
    //             vec![],
    //         ),
    //     ) {
    //         report.print_reports(&mut source_map, &analyzer);
    //     }
    //     println!();
    // });
}
