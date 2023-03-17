mod helpers;
use helpers::*;

#[test]
fn test_bitwise() {
    let path_str = "./test_data/bitwise.sol".to_string();
    let sol = include_str!("./test_data/bitwise.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_cast() {
    let path_str = "./test_data/cast.sol".to_string();
    let sol = include_str!("./test_data/cast.sol");
    assert_no_ctx_killed(path_str, sol);
}

// #[test]
// fn test_dyn_types() {
//     let path_str = "./test_data/dyn_types.sol".to_string();
// 	let sol = include_str!("./test_data/dyn_types.sol");
// 	assert_no_ctx_killed(path_str, sol);
// }

#[test]
fn test_env() {
    let path_str = "./test_data/env.sol".to_string();
    let sol = include_str!("./test_data/env.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_function_calls() {
    let path_str = "./test_data/function_calls.sol".to_string();
    let sol = include_str!("./test_data/function_calls.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_logical() {
    let path_str = "./test_data/logical.sol".to_string();
    let sol = include_str!("./test_data/logical.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_loops() {
    let path_str = "./test_data/loops.sol".to_string();
    let sol = include_str!("./test_data/loops.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_math() {
    let path_str = "./test_data/math.sol".to_string();
    let sol = include_str!("./test_data/math.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_modifier() {
    let path_str = "./test_data/modifier.sol".to_string();
    let sol = include_str!("./test_data/modifier.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_require() {
    let path_str = "./test_data/require.sol".to_string();
    let sol = include_str!("./test_data/require.sol");
    assert_no_ctx_killed(path_str, sol);
}

#[test]
fn test_using() {
    let path_str = "./test_data/using.sol".to_string();
    let sol = include_str!("./test_data/using.sol");
    assert_no_ctx_killed(path_str, sol);
}
