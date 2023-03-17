use pyrometer::Analyzer;
use shared::analyzer::Search;
use shared::{nodes::FunctionNode, Edge};

pub fn assert_no_ctx_killed(path_str: String, sol: &str) {
    let mut analyzer = Analyzer::default();
    let (maybe_entry, mut all_sources) = analyzer.parse(sol);
    all_sources.push((maybe_entry, path_str, sol.to_string(), 0));
    let entry = maybe_entry.unwrap();

    let funcs = analyzer.search_children(entry, &Edge::Func);
    for func in funcs.into_iter() {
        if let Some(ctx) = FunctionNode::from(func).maybe_body_ctx(&analyzer) {
            assert!(ctx.killed_loc(&analyzer).is_none());
            ctx.underlying(&analyzer)
                .children
                .iter()
                .for_each(|subctx| {
                    assert!(subctx.killed_loc(&analyzer).is_none());
                });
        }
    }
}
