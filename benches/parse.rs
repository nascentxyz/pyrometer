use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use pyrometer::{Analyzer, SourcePath};
use std::path::PathBuf;

use std::env::{self};
use std::fs;

criterion_group! {benches, bench}
criterion_main!(benches);

/// Returns a vector of solidity source file targets to be analyzed.
///
/// Each target is represented as a tuple consisting of:
/// - a string with the name of the target,
/// - a `PathBuf` representing the path to the target's source code file,
/// - an integer representing the sample size for the benchmark.
///
/// # Arguments
///
/// * `bench_contracts_root` - A `PathBuf` representing the root directory of the benchmarks.
///
/// # Returns
///
/// A vector of tuples representing the targets.
fn get_targets(bench_contracts_root: PathBuf) -> Vec<(String, PathBuf, usize)> {
    let mut targets = vec![];
    targets.push((
        "ctoken".to_string(),
        bench_contracts_root.join("flat_ctoken.sol"),
        50, // range of tens ms
    ));
    targets.push((
        "comptroller".to_string(),
        bench_contracts_root.join("flat_comptroller.sol"),
        10, // range of singles seconds. 10 samples is lowest
    ));

    targets
}

/// Runs the benchmarks.
///
/// This function iterates over all targets, reads the Solidity source code from the respective
/// file (excluding this operation from the benchmark), and runs the benchmark for the `parse`
/// function with the given sample size.
///
/// # Arguments
///
/// * `c` - A mutable reference to the Criterion object used for benchmarking.
fn bench(c: &mut Criterion) {
    let bench_contracts_root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap())
        .join("tests")
        .join("benches");
    let targets_vec = get_targets(bench_contracts_root.clone());

    for (name, path, sample_size) in targets_vec {
        // Excluding fs string read from benchmark. We want to benchmark the parsing for performance.
        let mut parsing_group = c.benchmark_group(name);
        parsing_group.sample_size(sample_size);
        let sol = fs::read_to_string(path.clone()).expect("Could not find file");
        let bench_id = BenchmarkId::new("parse", sample_size);
        parsing_group.bench_with_input(bench_id, &(path, &sol), |b, (path, &ref sol)| {
            b.iter(|| parse(path, sol.clone()));
        });
        parsing_group.finish();
    }
}

/// Parses the given Solidity source code using pyrometer.
///
/// # Arguments
///
/// * `path` - A `PathBuf` representing the path to the source code file.
/// * `sol` - A string containing the Solidity source code.
fn parse(path: &PathBuf, sol: String) {
    let mut analyzer = Analyzer::default();
    let current_path = SourcePath::SolidityFile(path.clone());
    let (_maybe_entry, mut _all_sources) = analyzer.parse(&sol, &current_path, true);
}
