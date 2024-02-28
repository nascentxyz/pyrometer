use graph::nodes::{Builtin, Function, FunctionParam, FunctionReturn};
use shared::{AnalyzerLike, GraphLike, StorageLocation};

use solang_parser::pt::{FunctionAttribute, Identifier, Loc, Visibility};

use ahash::AHashMap;

macro_rules! builtin_fn {
    ($($field:ident : $value:expr),* $(,)?) => {
        Function {
            $(
                $field: $value,
            )*
            ..Default::default()
        }
    }
}

// A list of all Solidity builtins functions
pub fn builtin_fns() -> AHashMap<String, Function> {
    let funcs = [
        builtin_fn!(
             name: Some(Identifier {
                loc: Loc::Builtin,
                name: "wrap".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
             name: Some(Identifier {
                loc: Loc::Builtin,
                name: "unwrap".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "concat".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "addmod".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "mulmod".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "balance".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "code".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "push".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "pop".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "ecrecover".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "type".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "assert".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "require".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "require_str".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "revert".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "revert_str".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "selfdestruct".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "keccak256".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "ripemd160".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "sha256".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "gasleft".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "blockhash".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.decode".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encode".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodePacked".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeWithSelector".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeWithSignature".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeCall".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "delegatecall".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "call".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "staticcall".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "transfer".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
        builtin_fn!(
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "send".to_string(),
            }),
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
        ),
    ];
    funcs
        .into_iter()
        .map(|func| (func.name.clone().expect("").name, func))
        .collect()
}

pub fn builtin_fns_inputs(
    analyzer: &mut (impl GraphLike + AnalyzerLike<Builtin = graph::nodes::Builtin>),
) -> AHashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)> {
    let funcs = [
        ("wrap", vec![], vec![]),
        ("unwrap", vec![], vec![]),
        (
            "addmod",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                storage: None,
                name: None,
            }],
        ),
        (
            "mulmod",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 0,
                    storage: None,
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                storage: None,
                name: None,
            }],
        ),
        (
            "balance",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Address),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                storage: None,
                name: None,
            }],
        ),
        (
            "code",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Address),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: None,
                name: None,
            }],
        ),
        (
            "codehash",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Address),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: None,
                name: None,
            }],
        ),
        ("concat", vec![], vec![]),
        ("push", vec![], vec![]),
        ("pop", vec![], vec![]),
        (
            "ecrecover",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                    order: 1,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                    order: 2,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(8)),
                    order: 3,
                    storage: None,
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Address),
                storage: None,
                name: None,
            }],
        ),
        ("type", vec![], vec![]),
        (
            "assert",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bool),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![],
        ),
        (
            "require",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bool),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![],
        ),
        (
            "require_str",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Bool),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::String),
                    order: 1,
                    storage: Some(StorageLocation::Memory(Loc::Implicit)),
                    name: None,
                },
            ],
            vec![],
        ),
        ("revert", vec![], vec![]),
        (
            "revert_str",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::String),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![],
        ),
        (
            "selfdestruct",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Address),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![],
        ),
        (
            "keccak256",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                storage: None,
                name: None,
            }],
        ),
        (
            "ripemd160",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bytes(20)),
                storage: None,
                name: None,
            }],
        ),
        (
            "sha256",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                storage: None,
                name: None,
            }],
        ),
        (
            "gasleft",
            vec![],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Uint(64)),
                storage: None,
                name: None,
            }],
        ),
        (
            "blockhash",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Uint(64)),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bytes(32)),
                storage: None,
                name: None,
            }],
        ),
        (
            "abi.decode",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                order: 0,
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
            vec![],
        ),
        (
            "abi.encode",
            vec![],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "abi.encodePacked",
            vec![],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "abi.encodeWithSelector",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bytes(4)),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "abi.encodeWithSignature",
            vec![FunctionParam {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::String),
                order: 0,
                storage: None,
                name: None,
            }],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        ("abi.encodeCall", vec![], vec![]),
        (
            "delegatecall",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Address),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                    order: 1,
                    storage: Some(StorageLocation::Memory(Loc::Implicit)),
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "call",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Address),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                    order: 1,
                    storage: Some(StorageLocation::Memory(Loc::Implicit)),
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "staticcall",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Address),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                    order: 1,
                    storage: Some(StorageLocation::Memory(Loc::Implicit)),
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::DynamicBytes),
                storage: Some(StorageLocation::Memory(Loc::Implicit)),
                name: None,
            }],
        ),
        (
            "transfer",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Address),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 1,
                    storage: None,
                    name: None,
                },
            ],
            vec![],
        ),
        (
            "send",
            vec![
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Address),
                    order: 0,
                    storage: None,
                    name: None,
                },
                FunctionParam {
                    loc: Loc::Builtin,
                    ty: analyzer.builtin_or_add(Builtin::Uint(256)),
                    order: 1,
                    storage: None,
                    name: None,
                },
            ],
            vec![FunctionReturn {
                loc: Loc::Builtin,
                ty: analyzer.builtin_or_add(Builtin::Bool),
                storage: None,
                name: None,
            }],
        ),
    ];

    funcs
        .into_iter()
        .map(|(name, inputs, outputs)| (name.to_string(), (inputs, outputs)))
        .collect()
}
