use crate::Builtin;
use crate::{AnalyzerLike, Function, FunctionParam, FunctionReturn};
use solang_parser::pt::{
    FunctionAttribute, FunctionTy, Identifier, Loc, StorageLocation, Visibility,
};
use std::collections::HashMap;

// A list of all Solidity builtins functions
pub fn builtin_fns() -> HashMap<String, Function> {
    let funcs = [
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "ecrecover".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::External(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "type".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "assert".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "require".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "require_str".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "revert".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "revert_str".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "selfdestruct".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "keccak256".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "ripemd160".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "sha256".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "gasleft".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "blockhash".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.decode".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encode".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodePacked".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeWithSelector".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeWithSignature".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
        Function {
            body: None,
            loc: Loc::Builtin,
            ty: FunctionTy::Function,
            name: Some(Identifier {
                loc: Loc::Builtin,
                name: "abi.encodeCall".to_string(),
            }),
            name_loc: Loc::Builtin,
            attributes: vec![FunctionAttribute::Visibility(Visibility::Internal(Some(
                Loc::Builtin,
            )))],
            params: vec![],
            returns: vec![],
        },
    ];
    funcs
        .into_iter()
        .map(|func| (func.name.clone().expect("").name, func))
        .collect()
}

pub fn builtin_fns_inputs(
    analyzer: &mut impl AnalyzerLike,
) -> HashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)> {
    let funcs = [
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
    ];

    funcs
        .into_iter()
        .map(|(name, inputs, outputs)| (name.to_string(), (inputs, outputs)))
        .collect()
}
