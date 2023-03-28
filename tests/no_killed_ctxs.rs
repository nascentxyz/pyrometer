use std::env;
mod helpers;
use helpers::*;

#[test]
fn test_bitwise() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/bitwise.sol", manifest_dir);
    let sol = include_str!("./test_data/bitwise.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_cast() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/cast.sol", manifest_dir);
    let sol = include_str!("./test_data/cast.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_dyn_types() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/dyn_types.sol", manifest_dir);
    let sol = include_str!("./test_data/dyn_types.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_env() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/env.sol", manifest_dir);
    let sol = include_str!("./test_data/env.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_function_calls() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/function_calls.sol", manifest_dir);
    let sol = include_str!("./test_data/function_calls.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_logical() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/logical.sol", manifest_dir);
    let sol = include_str!("./test_data/logical.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_loops() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/loops.sol", manifest_dir);
    let sol = include_str!("./test_data/loops.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_math() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/math.sol", manifest_dir);
    let sol = include_str!("./test_data/math.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_modifier() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/modifier.sol", manifest_dir);
    let sol = include_str!("./test_data/modifier.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_require() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/require.sol", manifest_dir);
    let sol = include_str!("./test_data/require.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_using() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/using.sol", manifest_dir);
    let sol = include_str!("./test_data/using.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_relative_import() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!(
        "{}/tests/test_data/relative_imports/relative_import.sol",
        manifest_dir
    );
    let sol = include_str!("./test_data/relative_imports/relative_import.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_remapping_import() {
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let path_str = format!("{}/tests/test_data/remapping_import.sol", manifest_dir);
    let sol = include_str!("./test_data/remapping_import.sol");
    remapping_assert_no_ctx_killed(
        path_str,
        format!("{}/tests/test_data/remappings.txt", manifest_dir),
        sol,
    );
}
