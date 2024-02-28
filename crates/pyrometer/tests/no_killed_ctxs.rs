use std::env;
mod helpers;
use helpers::*;

#[test]
fn test_bitwise() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/bitwise.sol");
    let sol = include_str!("./test_data/bitwise.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_cast() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/cast.sol");
    let sol = include_str!("./test_data/cast.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_dyn_types() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/dyn_types.sol");
    let sol = include_str!("./test_data/dyn_types.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_env() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/env.sol");
    let sol = include_str!("./test_data/env.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_function_calls() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/function_calls.sol");
    let sol = include_str!("./test_data/function_calls.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_logical() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/logical.sol");
    let sol = include_str!("./test_data/logical.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_loops() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/loops.sol");
    let sol = include_str!("./test_data/loops.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_math() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/math.sol");
    let sol = include_str!("./test_data/math.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_modifier() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/modifier.sol");
    let sol = include_str!("./test_data/modifier.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_require() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/require.sol");
    let sol = include_str!("./test_data/require.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_using() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/using.sol");
    let sol = include_str!("./test_data/using.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_storage() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/storage.sol");
    let sol = include_str!("./test_data/storage.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_named_func_call() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/named_func_call.sol");
    let sol = include_str!("./test_data/named_func_call.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_func_override() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/func_override.sol");
    let sol = include_str!("./test_data/func_override.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_intrinsics() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/intrinsics.sol");
    let sol = include_str!("./test_data/intrinsics.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_relative_import() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/relative_imports/relative_import.sol");
    let sol = include_str!("./test_data/relative_imports/relative_import.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_constructor() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/constructor.sol");
    let sol = include_str!("./test_data/constructor.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_interface() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/interface.sol");
    let sol = include_str!("./test_data/interface.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_const_var() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/const_var.sol");
    let sol = include_str!("./test_data/const_var.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_abstract() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/abstract.sol");
    let sol = include_str!("./test_data/abstract.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_remapping_import() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/remapping_import.sol");
    let sol = include_str!("./test_data/remapping_import.sol");
    remapping_assert_no_ctx_killed(
        path_str,
        format!("{manifest_dir}/tests/test_data/remappings.txt"),
        sol,
    );
}

#[test]
fn test_repros() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{manifest_dir}/tests/test_data/repros/");
    let paths = std::fs::read_dir(path_str).unwrap();
    for path in paths {
        let path_str = path.unwrap().path().display().to_string();
        println!("checking parse errors in: {path_str}");
        assert_no_parse_errors(path_str);
    }
}
