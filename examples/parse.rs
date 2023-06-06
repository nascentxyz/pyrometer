use pyrometer::{Analyzer, SourcePath};
use std::path::PathBuf;

use std::fs;

fn main() {
    let bench_contracts_root = PathBuf::from("./tests/benches");

    let comptroller_path = &bench_contracts_root.join("flat_ctoken.sol");

    let sol = fs::read_to_string(comptroller_path).expect("Could not find file");


    let mut analyzer = Analyzer::default();
    let current_path = SourcePath::SolidityFile(comptroller_path.clone());
    let (_maybe_entry, mut _all_sources) = analyzer.parse(&sol, &current_path, true);
}
