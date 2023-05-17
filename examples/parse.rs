use pyrometer::Analyzer;
use std::path::PathBuf;

use std::fs;

fn main() {
    let bench_contracts_root = PathBuf::from("./tests/benches");

    let comptroller_path = &bench_contracts_root.join("flat_ctoken.sol");

    let sol = fs::read_to_string(comptroller_path).expect("Could not find file");

    let mut analyzer = Analyzer {
        root: bench_contracts_root.clone(),
        ..Default::default()
    };
    let (_maybe_entry, mut _all_sources) = analyzer.parse(&sol, &bench_contracts_root, true);
}
