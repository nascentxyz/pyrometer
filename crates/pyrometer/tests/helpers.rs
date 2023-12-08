use analyzers::FunctionVarsBoundAnalyzer;
use analyzers::ReportConfig;
use analyzers::ReportDisplay;
use ariadne::sources;
use graph::{nodes::FunctionNode, Edge};
use pyrometer::{Analyzer, SourcePath};
use shared::NodeIdx;
use shared::Search;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::path::PathBuf;

pub fn assert_no_ctx_killed(path_str: String, sol: &str) {
    let mut analyzer = Analyzer::default();
    let current_path = SourcePath::SolidityFile(PathBuf::from(path_str.clone()));
    let maybe_entry = analyzer.parse(sol, &current_path, true);
    let entry = maybe_entry.unwrap();
    no_ctx_killed(analyzer, entry);
}

pub fn remapping_assert_no_ctx_killed(path_str: String, remapping_file: String, sol: &str) {
    let mut analyzer = Analyzer::default();
    analyzer.set_remappings_and_root(remapping_file);
    let current_path = SourcePath::SolidityFile(PathBuf::from(path_str.clone()));
    let maybe_entry = analyzer.parse(sol, &current_path, true);
    let entry = maybe_entry.unwrap();
    no_ctx_killed(analyzer, entry);
}

pub fn no_ctx_killed(mut analyzer: Analyzer, entry: NodeIdx) {
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
