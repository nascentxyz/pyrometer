use ariadne::sources;
use pyrometer::context::analyzers::ReportConfig;
use pyrometer::context::analyzers::{FunctionVarsBoundAnalyzer, ReportDisplay};
use pyrometer::Analyzer;
use shared::analyzer::Search;
use shared::NodeIdx;
use shared::{nodes::FunctionNode, Edge};
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::path::PathBuf;

pub fn assert_no_ctx_killed(path_str: String, sol: &str) {
    let mut analyzer = Analyzer::default();
    let (maybe_entry, mut all_sources) =
        analyzer.parse(sol, &PathBuf::from(path_str.clone()), true);
    all_sources.push((maybe_entry, path_str.clone(), sol.to_string(), 0));
    let entry = maybe_entry.unwrap();
    no_ctx_killed(analyzer, entry, path_str, all_sources);
}

pub fn remapping_assert_no_ctx_killed(path_str: String, remapping_file: String, sol: &str) {
    let mut analyzer = Analyzer::default();
    analyzer.set_remappings_and_root(remapping_file);
    let (maybe_entry, mut all_sources) =
        analyzer.parse(sol, &PathBuf::from(path_str.clone()), true);
    all_sources.push((maybe_entry, path_str.clone(), sol.to_string(), 0));
    let entry = maybe_entry.unwrap();
    no_ctx_killed(analyzer, entry, path_str, all_sources);
}

pub fn no_ctx_killed(
    mut analyzer: Analyzer,
    entry: NodeIdx,
    path_str: String,
    all_sources: Vec<(Option<NodeIdx>, String, String, usize)>,
) {
    assert!(
        analyzer.expr_errs.is_empty(),
        "Analyzer encountered parse errors"
    );

    let config = ReportConfig {
        eval_bounds: true,
        simplify_bounds: false,
        show_tmps: true,
        show_consts: true,
        show_symbolics: true,
        show_initial_bounds: true,
        show_all_lines: true,
        show_reverts: true,
        show_unreachables: true,
        show_nonreverts: true,
    };
    let file_mapping: BTreeMap<_, _> = vec![(0usize, path_str)].into_iter().collect();

    let mut source_map = sources(
        all_sources
            .iter()
            .map(|(_entry, name, src, _num)| (name.clone(), src))
            .collect::<HashMap<_, _>>(),
    );

    let funcs = analyzer.search_children(entry, &Edge::Func);
    for func in funcs.into_iter() {
        if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&mut analyzer) {
            if ctx.killed_loc(&analyzer).unwrap().is_some() {
                analyzer
                    .bounds_for_all(&file_mapping, ctx, config)
                    .as_cli_compat(&file_mapping)
                    .print_reports(&mut source_map, &analyzer);
                panic!("Killed context in test");
            }
            ctx.all_edges(&analyzer).unwrap().iter().for_each(|subctx| {
                if subctx.killed_loc(&analyzer).unwrap().is_some() {
                    analyzer
                        .bounds_for_all(&file_mapping, *subctx, config)
                        .as_cli_compat(&file_mapping)
                        .print_reports(&mut source_map, &analyzer);
                    panic!("Killed context in test");
                }
            });
        }
    }
}
