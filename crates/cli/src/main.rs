use analyzers::{FunctionVarsBoundAnalyzer, ReportConfig, ReportDisplay};
use graph::{
    nodes::{ContractNode, FunctionNode},
    solvers::{AtomicSolveStatus, BruteBinSearchSolver, SolcSolver},
    Edge,
};
use pyrometer::{Analyzer, Root, SourcePath};
use reqwest::Client;
use shared::{post_to_site, Search};
use shared::{GraphDot, USE_DEBUG_SITE};

use ariadne::sources;
use clap::{ArgAction, Parser, ValueHint};

use tracing::{error, trace};
use tracing_subscriber::{prelude::*, Registry};

use std::{
    collections::{BTreeMap, HashMap},
    env::{self},
    fs,
    path::PathBuf,
};
use tokio::runtime::Runtime;

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
    pub mermaid: bool,
    /// Whether to print out a dot string of the analyzed contracts
    #[clap(long, short, default_value = "false")]
    pub dot: bool,
    /// Whether to generate and open a dot visualization of the analyzed contracts
    #[clap(long, short, default_value = "false")]
    pub open_dot: bool,
    /// Whether to generate and open a mermaid visualization of the analyzed contracts
    #[clap(long, default_value = "false")]
    pub open_mermaid: bool,
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
    /// A debugging command to prevent bound analysis printing. Useful for debugging parse errors during development. Only prints out parse errors
    /// then ends the program
    #[clap(long)]
    pub debug: bool,

    /// Forces a panic on first error encountered
    #[clap(long)]
    pub debug_panic: bool,

    /// Max stack depth to evaluate to
    #[clap(long, default_value = "200")]
    pub max_stack_depth: usize,

    /// Print stats about the IR
    #[clap(long)]
    pub stats: bool,

    /// Post pyrometer debugging information to debugging site
    #[clap(long)]
    pub debug_site: bool,

    #[clap(long)]
    pub minimize_debug: Option<String>,
}

pub fn subscriber() {
    tracing_subscriber::Registry::default()
        .with(tracing_subscriber::filter::EnvFilter::from_default_env())
        .with(tracing_subscriber::fmt::layer())
        .init()
}

pub fn tree_subscriber() {
    let subscriber = Registry::default()
        .with(
            tracing_tree::HierarchicalLayer::default()
                .with_indent_lines(true)
                .with_indent_amount(1)
                // .with_targets(true)
                .with_thread_names(false), // .with_thread_ids(true)
                                           // .with_verbose_exit(true)
                                           // .with_verbose_entry(true)
                                           //   .with_targets(true)
        )
        .with(tracing_subscriber::filter::EnvFilter::from_default_env());
    tracing::subscriber::set_global_default(subscriber).unwrap();
}

fn main() {
    tree_subscriber();
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

    let mut analyzer = Analyzer {
        max_depth: args.max_stack_depth,
        root: Root::RemappingsDirectory(env::current_dir().unwrap()),
        debug_panic: args.debug_panic || args.minimize_debug.is_some(),
        minimize_debug: args.minimize_debug,
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
        let (current_path, sol, _, _) = analyzer.sources.first().unwrap().clone();
        (current_path, sol)
    } else {
        panic!("Unsupported file type")
    };

    let mut arena_base = Default::default();
    let arena = &mut arena_base;

    if args.debug_site {
        unsafe {
            USE_DEBUG_SITE = true;
        }

        let rt = Runtime::new().unwrap();
        rt.block_on(async {
            let client = Client::new();
            let res = client
                .post("http://127.0.0.1:8545/clear")
                .send()
                .await
                .expect("Failed to send request");

            if res.status().is_success() {
                trace!("Successfully cleared history of site");
            } else {
                error!("Failed to clear history of site: {:?}", res.status());
            }
        });
        post_to_site(&analyzer, arena);
    }

    let t0 = std::time::Instant::now();
    let maybe_entry = analyzer.parse(arena, &sol, &current_path, true);
    let t_end = t0.elapsed();
    let parse_time = t_end.as_millis();

    println!("DONE ANALYZING IN: {parse_time}ms. Writing to cli...");

    // println!("Arena: {:#?}", analyzer.range_arena);
    if unsafe { USE_DEBUG_SITE } {
        use pyrometer::graph_backend::mermaid_str;
        use pyrometer::graph_backend::post_to_site_arena;
        use pyrometer::graph_backend::Elems;
        let elems = Elems::try_from(&*arena);
        match elems {
            Ok(elems) => {
                let elems_graph = elems.to_graph(&analyzer, arena);
                let elems_graph_mermaid_str = mermaid_str(&elems_graph);
                post_to_site_arena(elems_graph_mermaid_str);
            }
            Err(e) => {
                eprintln!("Can't post arena, error creating Elems: {:?}", e);
            }
        };

        // post the graph to the site
        post_to_site(&analyzer, arena);
    }

    if args.stats {
        println!("{}", analyzer.stats(t_end, arena));
    }
    // println!("Arena: {:#?}", analyzer.range_arena);

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

    let entry = maybe_entry.unwrap();

    // analyzer.print_errors(&file_mapping, &mut source_map);

    // let t = petgraph::algo::toposort(&analyzer.graph, None);
    analyzer.print_errors(&file_mapping, &mut source_map);

    if args.open_dot {
        analyzer.open_dot(arena)
    }

    if args.dot {
        println!("{}", analyzer.dot_str_no_tmps(arena));
    }

    if args.mermaid {
        println!("{}", analyzer.mermaid_str(arena));
    }

    if args.open_mermaid {
        analyzer.open_mermaid(arena);
    }

    // println!("{}", analyzer.range_arena.ranges.iter().map(|i| {
    //     let j = i.borrow();
    //     let (min_cached, max_cached) = j.is_min_max_cached(&analyzer);
    //     format!("\t{j}, is cached: {min_cached}, {max_cached}\n")
    // }).collect::<Vec<_>>().join(""));
    // println!("{}", analyzer.range_arena.map.iter().map(|(k, v)| {
    //     format!("\t{}: {}\n", k, v)
    // }).collect::<Vec<_>>().join(""));

    if args.debug {
        return;
    }

    // println!("getting contracts");
    let all_contracts = analyzer
        .search_children(entry, &Edge::Contract)
        .into_iter()
        .map(ContractNode::from)
        .collect::<Vec<_>>();

    // TODO: clean this up to actually run on all contracts
    // if args.swq {
    // println!("Creating SWQ graph for {} contracts", all_contracts.len());
    // let mut cond_graph: Option<ConditionGraph> = None;
    // for i in 0..all_contracts.len() {
    //     match (&mut cond_graph, analyzer.func_query(all_contracts[i])) {
    //         (Some(ref mut existing), Some(new)) => {
    //             existing.append_graph(new);
    //         }
    //         (None, Some(new)) => {
    //             cond_graph = Some(new);
    //         }
    //         _ => {}
    //     }
    // }

    // if let Some(graph) = cond_graph {
    //     println!("{}", graph.dot_str());
    //     graph.open_dot();
    // } else {
    //     println!("no graph");
    // }
    // } else if args.swq_mermaid {
    // println!("Creating SWQ graph for {} contracts", all_contracts.len());
    // let mut cond_graph: Option<ConditionGraph> = None;
    // for i in 0..all_contracts.len() {
    //     match (&mut cond_graph, analyzer.func_query(all_contracts[i])) {
    //         (Some(ref mut existing), Some(new)) => {
    //             existing.append_graph(new);
    //         }
    //         (None, Some(new)) => {
    //             cond_graph = Some(new);
    //         }
    //         _ => {}
    //     }
    // }

    // if let Some(graph) = cond_graph {
    //     println!("{}", graph.mermaid_str());
    // } else {
    //     println!("no graph");
    // }
    // } else {
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
                        let mut all_edges = ctx.all_edges(&analyzer).unwrap();
                        all_edges.push(ctx);
                        all_edges.iter().for_each(|c| {
                            let _rets = c.return_nodes(&analyzer).unwrap();
                            // if c.path(&analyzer).starts_with(r#"step(uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64)"#)
                            // && rets.iter().take(1).any(|ret| {
                            //     let range = ret.1.ref_range(&analyzer).unwrap().unwrap();
                            //     range.evaled_range_min(&analyzer).unwrap().range_eq(&Elem::from(Concrete::from(I256::from(-1))))
                            // })
                            {
                                // step(uint64, uint64, uint64, uint64, uint64, uint64, uint64, uint64).fork{ false }.fork{ true }.fork{ true }.fork{ false }"#.to_string()) {
                                // println!("{:#?}", c.ctx_deps_as_controllables_str(&analyzer).unwrap());
                                if let Some(mut solver) = BruteBinSearchSolver::maybe_new(
                                    c.ctx_deps(&analyzer).unwrap(),
                                    &mut analyzer,
                                    arena,
                                )
                                .unwrap()
                                {
                                    match solver.solve(&mut analyzer, arena).unwrap() {
                                        AtomicSolveStatus::Unsat => {
                                            println!("TRUE UNSAT: {}", c.path(&analyzer));
                                        }
                                        AtomicSolveStatus::Sat(ranges) => {
                                            // println!("-----------------------");
                                            // println!("sat for: {}", c.path(&analyzer));
                                            ranges.iter().for_each(|(atomic, conc)| {
                                                println!(
                                                    "{}: {}",
                                                    atomic.idxs[0].display_name(&analyzer).unwrap(),
                                                    conc.as_human_string()
                                                );
                                            });
                                        }
                                        AtomicSolveStatus::Indeterminate => {
                                            // println!("-----------------------");
                                            // println!("sat for: {}", c.path(&analyzer));
                                            // println!("MAYBE UNSAT");
                                        }
                                    }
                                }
                                // println!("-----------------------");
                                let analysis = analyzer
                                    .bounds_for_lineage(arena, &file_mapping, *c, vec![*c], config)
                                    .as_cli_compat(&file_mapping);
                                analysis.print_reports(&mut source_map, &analyzer, arena);
                                // return;
                            }
                        });
                    }
                }
            } else if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&mut analyzer) {
                if !matches!(
                    ctx.underlying(&analyzer).unwrap().killed,
                    Some((_, graph::nodes::KilledKind::DebugIgnored))
                ) {
                    let analysis = analyzer
                        .bounds_for_all(arena, &file_mapping, ctx, config)
                        .as_cli_compat(&file_mapping);
                    analysis.print_reports(&mut source_map, &analyzer, arena);
                }
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
                                .bounds_for_all(arena, &file_mapping, ctx, config)
                                .as_cli_compat(&file_mapping);
                            analysis.print_reports(&mut source_map, &analyzer, arena);
                        }
                    } else {
                        let ctx = func.body_ctx(&mut analyzer);
                        let analysis = analyzer
                            .bounds_for_all(arena, &file_mapping, ctx, config)
                            .as_cli_compat(&file_mapping);
                        analysis.print_reports(&mut source_map, &analyzer, arena);
                    }
                }
            });
    }
    // }

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
