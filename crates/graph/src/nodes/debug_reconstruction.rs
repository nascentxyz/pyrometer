use crate::{
    nodes::{ContractNode, EnumNode, ErrorNode, FunctionNode, StructNode, TyNode, VarNode},
    AnalyzerBackend, Edge, TypeNode,
};

use shared::GraphError;

use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::Loc;

use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct FuncReconstructionReqs {
    pub storage: Vec<VarNode>,
    pub usertypes: Vec<TypeNode>,
}

impl FuncReconstructionReqs {
    pub fn enums(&self) -> Vec<EnumNode> {
        self.usertypes
            .iter()
            .filter_map(|ut| {
                if let TypeNode::Enum(ret) = ut {
                    Some(*ret)
                } else {
                    None
                }
            })
            .collect()
    }
    pub fn structs(&self) -> Vec<StructNode> {
        self.usertypes
            .iter()
            .filter_map(|ut| {
                if let TypeNode::Struct(ret) = ut {
                    Some(*ret)
                } else {
                    None
                }
            })
            .collect()
    }
    pub fn errs(&self) -> Vec<ErrorNode> {
        self.usertypes
            .iter()
            .filter_map(|ut| {
                if let TypeNode::Error(ret) = ut {
                    Some(*ret)
                } else {
                    None
                }
            })
            .collect()
    }
    pub fn tys(&self) -> Vec<TyNode> {
        self.usertypes
            .iter()
            .filter_map(|ut| {
                if let TypeNode::Ty(ret) = ut {
                    Some(*ret)
                } else {
                    None
                }
            })
            .collect()
    }
}

impl ContractNode {
    pub fn reconstruct_name_src<'a>(
        &self,
        analyzer: &'a impl AnalyzerBackend,
    ) -> Result<&'a str, GraphError> {
        let mut loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        let name_loc = self.underlying(analyzer)?.name.clone().unwrap().loc;
        loc.use_end_from(&name_loc);
        Ok(&analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()])
    }

    pub fn reconstruct_inherits(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let used_inherits = self
            .direct_inherited_contracts(analyzer)
            .iter()
            .filter_map(|inherited| {
                if contract_to_funcs.contains_key(&Some(*inherited)) {
                    Some(inherited.name(analyzer).unwrap())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        if used_inherits.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!("is {}", used_inherits.join(", ")))
        }
    }

    pub fn reconstruct_usings(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let contract_to_using_locs = contract_to_funcs
            .keys()
            .filter_map(|maybe_c| {
                Some((
                    (*maybe_c)?,
                    analyzer
                        .graph()
                        .edges_directed((*maybe_c)?.0.into(), petgraph::Direction::Outgoing)
                        .filter(|edge| matches!(*edge.weight(), Edge::UsingContract(_)))
                        .filter(|edge| {
                            contract_to_funcs.contains_key(&Some(ContractNode::from(edge.target())))
                        })
                        .map(|edge| {
                            let Edge::UsingContract(loc) = edge.weight() else {
                                panic!("here")
                            };
                            *loc
                        })
                        .collect::<Vec<Loc>>(),
                ))
            })
            .collect::<BTreeMap<ContractNode, Vec<Loc>>>();

        let mut using_str = Default::default();
        if let Some(locs) = contract_to_using_locs.get(self) {
            using_str = locs
                .iter()
                .map(|loc| {
                    let file_no = loc.try_file_no().unwrap();
                    format!(
                        "{};",
                        &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
        }

        if using_str.is_empty() {
            Ok(using_str)
        } else {
            Ok(format!("    {using_str}\n"))
        }
    }

    pub fn reconstruct_funcs(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        if let Some(funcs_and_storage) = contract_to_funcs.get(&Some(*self)) {
            Ok(format!(
                "    {}\n",
                funcs_and_storage
                    .iter()
                    .map(|(func, _)| func.reconstruct_src(analyzer).unwrap())
                    .collect::<Vec<_>>()
                    .join("\n")
            ))
        } else {
            Ok("".to_string())
        }
    }

    pub fn reconstruct_storage(
        &self,
        analyzer: &impl AnalyzerBackend,
        used_storage: Vec<VarNode>,
    ) -> Result<String, GraphError> {
        if used_storage.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!(
                "    {}\n",
                self.direct_storage_vars(analyzer)
                    .iter()
                    .filter_map(|storage_var| {
                        if used_storage.contains(storage_var) {
                            Some(format!("{};", storage_var.reconstruct_src(analyzer).ok()?))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n    ")
            ))
        }
    }

    pub fn reconstruct_structs(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let mut used = contract_to_funcs
            .values()
            .flat_map(|func_and_vars| {
                func_and_vars
                    .iter()
                    .flat_map(|(_, reqs)| {
                        reqs.structs()
                            .iter()
                            .filter_map(|var| {
                                if var.maybe_associated_contract(analyzer) == Some(*self) {
                                    Some(*var)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<StructNode>>()
                    })
                    .collect::<Vec<StructNode>>()
            })
            .collect::<Vec<StructNode>>();
        used.sort_by(|a, b| a.0.cmp(&b.0));
        used.dedup();

        if used.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!(
                "    {}\n",
                self.structs(analyzer)
                    .iter()
                    .filter_map(|strukt| {
                        if used.contains(strukt) {
                            Some(strukt.reconstruct_src(analyzer).ok()?.to_string())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n    ")
            ))
        }
    }

    pub fn reconstruct_enums(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let mut used = contract_to_funcs
            .values()
            .flat_map(|func_and_vars| {
                func_and_vars
                    .iter()
                    .flat_map(|(_, reqs)| {
                        reqs.enums()
                            .iter()
                            .filter_map(|var| {
                                if var.maybe_associated_contract(analyzer) == Some(*self) {
                                    Some(*var)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<EnumNode>>()
                    })
                    .collect::<Vec<EnumNode>>()
            })
            .collect::<Vec<EnumNode>>();
        used.sort_by(|a, b| a.0.cmp(&b.0));
        used.dedup();

        if used.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!(
                "    {}\n",
                self.enums(analyzer)
                    .iter()
                    .filter_map(|enu| {
                        if used.contains(enu) {
                            Some(enu.reconstruct_src(analyzer).ok()?.to_string())
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n    ")
            ))
        }
    }

    pub fn reconstruct_tys(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let mut used = contract_to_funcs
            .values()
            .flat_map(|func_and_vars| {
                func_and_vars
                    .iter()
                    .flat_map(|(_, reqs)| {
                        reqs.tys()
                            .iter()
                            .filter_map(|var| {
                                if var.maybe_associated_contract(analyzer) == Some(*self) {
                                    Some(*var)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<TyNode>>()
                    })
                    .collect::<Vec<TyNode>>()
            })
            .collect::<Vec<TyNode>>();
        used.sort_by(|a, b| a.0.cmp(&b.0));
        used.dedup();

        if used.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!(
                "    {}\n",
                self.tys(analyzer)
                    .iter()
                    .filter_map(|ty| {
                        if used.contains(ty) {
                            Some(format!("{};", ty.reconstruct_src(analyzer).ok()?))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n    ")
            ))
        }
    }

    pub fn reconstruct_errs(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let mut used = contract_to_funcs
            .values()
            .flat_map(|func_and_vars| {
                func_and_vars
                    .iter()
                    .flat_map(|(_, reqs)| {
                        reqs.errs()
                            .iter()
                            .filter_map(|var| {
                                if var.maybe_associated_contract(analyzer) == Some(*self) {
                                    Some(*var)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<ErrorNode>>()
                    })
                    .collect::<Vec<ErrorNode>>()
            })
            .collect::<Vec<ErrorNode>>();
        used.sort_by(|a, b| a.0.cmp(&b.0));
        used.dedup();

        if used.is_empty() {
            Ok("".to_string())
        } else {
            Ok(format!(
                "    {}\n",
                self.errs(analyzer)
                    .iter()
                    .filter_map(|err| {
                        if used.contains(err) {
                            Some(format!("{};", err.reconstruct_src(analyzer).ok()?))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join("\n    ")
            ))
        }
    }

    pub fn reconstruct(
        &self,
        analyzer: &impl AnalyzerBackend,
        contract_to_funcs: &BTreeMap<
            Option<ContractNode>,
            Vec<(FunctionNode, FuncReconstructionReqs)>,
        >,
    ) -> Result<String, GraphError> {
        let mut used_storage = contract_to_funcs
            .values()
            .flat_map(|func_and_vars| {
                func_and_vars
                    .iter()
                    .flat_map(|(_, reqs)| {
                        reqs.storage
                            .iter()
                            .filter_map(|var| {
                                if var.maybe_associated_contract(analyzer) == Some(*self) {
                                    Some(*var)
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<VarNode>>()
                    })
                    .collect::<Vec<VarNode>>()
            })
            .collect::<Vec<VarNode>>();
        used_storage.sort_by(|a, b| a.0.cmp(&b.0));
        used_storage.dedup();

        let reconstructed_name = self.reconstruct_name_src(analyzer)?;
        let inherited = self.reconstruct_inherits(analyzer, contract_to_funcs)?;
        let usings = self.reconstruct_usings(analyzer, contract_to_funcs)?;
        let storage = self.reconstruct_storage(analyzer, used_storage)?;
        let structs = self.reconstruct_structs(analyzer, contract_to_funcs)?;
        let enums = self.reconstruct_enums(analyzer, contract_to_funcs)?;
        let tys = self.reconstruct_tys(analyzer, contract_to_funcs)?;
        let _errs = self.reconstruct_errs(analyzer, contract_to_funcs)?;
        let funcs = self.reconstruct_funcs(analyzer, contract_to_funcs)?;
        Ok(format!(
            "{reconstructed_name} {inherited} {{\n{usings}{structs}{enums}{tys}{storage}{funcs}\n}}"
        ))
    }

    pub fn using_contracts(&self, analyzer: &impl AnalyzerBackend) -> Vec<ContractNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .filter(|edge| matches!(*edge.weight(), Edge::UsingContract(_)))
            .map(|edge| ContractNode::from(edge.target()))
            .collect()
    }
}

impl FunctionNode {
    pub fn reconstruct_src(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();

        // let overriding = self.get_overriding(analyzer)?;
        if let Some(body_loc) = self.body_loc(analyzer)? {
            let body =
                &analyzer.file_mapping().get(&file_no).unwrap()[body_loc.start()..body_loc.end()];
            Ok(format!(
                "{} {body}",
                &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
            ))
        } else {
            Ok(format!(
                "{};",
                &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
            ))
        }
    }

    pub fn maybe_used_storage(&self, analyzer: &mut impl AnalyzerBackend) -> Option<Vec<VarNode>> {
        self.maybe_body_ctx(analyzer)
            .map(|body_ctx| body_ctx.contract_vars_referenced_global(analyzer))
    }

    pub fn maybe_used_usertypes(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Option<Vec<TypeNode>> {
        self.maybe_body_ctx(analyzer)
            .map(|body_ctx| body_ctx.usertype_vars_referenced_global(analyzer))
    }

    pub fn reconstruction_requirements(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> FuncReconstructionReqs {
        FuncReconstructionReqs {
            storage: self.maybe_used_storage(analyzer).unwrap_or_default(),
            usertypes: self.maybe_used_usertypes(analyzer).unwrap_or_default(),
        }
    }
}

impl TyNode {
    pub fn reconstruct_src(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        Ok(format!(
            "{};\n",
            &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
        ))
    }
}

impl EnumNode {
    pub fn reconstruct_src(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        Ok(format!(
            "{}\n",
            &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
        ))
    }
}

impl StructNode {
    pub fn reconstruct_src(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        Ok(format!(
            "{}\n",
            &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
        ))
    }
}

impl ErrorNode {
    pub fn reconstruct_src(&self, analyzer: &impl AnalyzerBackend) -> Result<String, GraphError> {
        let loc = self.underlying(analyzer)?.loc;
        let file_no = loc.try_file_no().unwrap();
        Ok(format!(
            "{};\n",
            &analyzer.file_mapping().get(&file_no).unwrap()[loc.start()..loc.end()]
        ))
    }
}
