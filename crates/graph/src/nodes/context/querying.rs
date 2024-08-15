use crate::{
    nodes::{
        ContextNode, ContractId, ContractNode, EnumNode, ErrorNode, FunctionNode, SourceUnitNode,
        SourceUnitPartNode, StructNode, TyNode,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend,
};

use shared::{GraphError, NodeIdx, Search};
use std::collections::{BTreeMap, BTreeSet};

impl ContextNode {
    /// Gets the associated contract for the function for the context
    pub fn associated_contract(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ContractNode, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer)
            .expect("No associated contract for context"))
    }

    /// Tries to get the associated function for the context
    pub fn maybe_associated_contract(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Option<ContractNode>, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer))
    }

    /// Tries to get the associated source for the context
    pub fn maybe_associated_source(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Option<SourceUnitNode> {
        let context = self.underlying(analyzer).unwrap();
        if let Some(src) = context.cache.associated_source {
            Some(src.into())
        } else if let Some(parent_ctx) = context.parent_ctx() {
            let src = parent_ctx.maybe_associated_source(analyzer)?;
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .associated_source = Some(src.into());
            Some(src)
        } else {
            let func = self.associated_fn(analyzer).unwrap();
            func.maybe_associated_source(analyzer)
        }
    }

    /// Tries to get the associated source unit part for the context
    pub fn associated_source_unit_part(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<SourceUnitPartNode, GraphError> {
        if let Some(sup) = self
            .associated_fn(analyzer)?
            .maybe_associated_source_unit_part(analyzer)
        {
            Ok(sup)
        } else {
            Err(GraphError::NodeConfusion(
                "Expected context to have an associated source but didnt".to_string(),
            ))
        }
    }

    pub fn contract_id(&self, analyzer: &impl GraphBackend) -> Result<ContractId, GraphError> {
        Ok(self.underlying(analyzer)?.contract_id)
    }

    pub fn keep_inscope_tys(
        &self,
        idxs: &mut Vec<NodeIdx>,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let mut tys = self
            .visible_structs(analyzer)?
            .iter()
            .map(|i| i.0.into())
            .collect::<Vec<_>>();
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            tys.extend(contract.visible_nodes(analyzer));
        }

        if let Some(source) = self.maybe_associated_source(analyzer) {
            tys.extend(source.visible_nodes(analyzer)?);
        }

        tys.sort();
        tys.dedup();

        idxs.retain(|i| tys.contains(i));

        Ok(())
    }

    /// Gets visible functions
    pub fn visible_modifiers(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        // TODO: filter privates
        let Some(source) = self.maybe_associated_source(analyzer) else {
            return Err(GraphError::NodeConfusion(
                "Expected context to have an associated source but didnt".to_string(),
            ));
        };
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            let mut modifiers = contract.modifiers(analyzer);
            // extend with free floating functions
            modifiers.extend(
                analyzer
                    .search_children_depth(source.into(), &Edge::Modifier, 1, 0)
                    .into_iter()
                    .map(FunctionNode::from)
                    .collect::<Vec<_>>(),
            );

            // extend with inherited functions
            let inherited_contracts = analyzer.search_children_exclude_via(
                contract.0.into(),
                &Edge::InheritedContract,
                &[Edge::Func],
            );
            modifiers.extend(
                inherited_contracts
                    .into_iter()
                    .flat_map(|inherited_contract| {
                        ContractNode::from(inherited_contract).modifiers(analyzer)
                    })
                    .collect::<Vec<_>>(),
            );

            let mut mapping: BTreeMap<String, BTreeSet<FunctionNode>> = BTreeMap::new();
            for modifier in modifiers.iter() {
                let entry = mapping.entry(modifier.name(analyzer)?).or_default();
                entry.insert(*modifier);
            }
            mapping
                .into_values()
                .map(|modifier_set| {
                    let as_vec = modifier_set.iter().collect::<Vec<_>>();

                    match as_vec.len() {
                        2 => {
                            as_vec[0].get_overriding(as_vec[1], analyzer)
                        }
                        3.. => {
                            panic!("3+ visible functions with the same name. This is invalid solidity, {as_vec:#?}")
                        }
                        _ => Ok(*as_vec[0])
                    }
                })
                .collect()
        } else {
            // we are in a free floating function, only look at free floating functions
            let Some(source) = self.maybe_associated_source(analyzer) else {
                return Err(GraphError::NodeConfusion(
                    "Expected context to have an associated source but didnt".to_string(),
                ));
            };
            Ok(analyzer
                .search_children_depth(source.into(), &Edge::Modifier, 1, 0)
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>())
        }
    }

    pub fn visible_constructors(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        if let Some(src) = self.maybe_associated_source(analyzer) {
            let contracts = src.visible_contracts(analyzer)?;
            Ok(contracts
                .iter()
                .filter_map(|contract| contract.constructor(analyzer))
                .collect())
        } else {
            Ok(vec![])
        }
    }

    /// Gets visible functions
    pub fn visible_funcs(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_funcs {
            return Ok(vis.clone());
        }
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            let mut mapping = contract.linearized_functions(analyzer, false)?;
            // extend with free floating functions
            mapping.extend(
                analyzer
                    .search_children_depth(analyzer.entry(), &Edge::Func, 2, 0)
                    .into_iter()
                    .filter_map(|i| {
                        let fn_node = FunctionNode::from(i);
                        if let Ok(name) = fn_node.name(analyzer) {
                            if !mapping.contains_key(&name) {
                                Some((name, fn_node))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .collect::<BTreeMap<_, _>>(),
            );
            let funcs: Vec<_> = mapping.values().copied().collect();
            self.underlying_mut(analyzer)?.cache.visible_funcs = Some(funcs.clone());
            Ok(funcs)
        } else {
            // we are in a free floating function, only look at free floating functions
            let funcs = analyzer
                .search_children_depth(analyzer.entry(), &Edge::Func, 2, 0)
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>();

            self.underlying_mut(analyzer)?.cache.visible_funcs = Some(funcs.clone());
            Ok(funcs)
        }
    }

    /// Gets all visible functions
    pub fn source_funcs(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Vec<FunctionNode> {
        // TODO: filter privates
        let Some(source) = self.maybe_associated_source(analyzer) else {
            return vec![];
        };
        analyzer
            .search_children_exclude_via(
                source.into(),
                &Edge::Func,
                &[
                    Edge::Context(ContextEdge::Context),
                    Edge::Context(ContextEdge::Variable),
                ],
            )
            .into_iter()
            .map(FunctionNode::from)
            .collect::<Vec<_>>()
    }

    /// Gets all visible structs
    pub fn visible_structs(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<StructNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_structs {
            return Ok(vis.clone());
        }

        let Some(source) = self.maybe_associated_source(analyzer) else {
            return Ok(vec![]);
        };

        let mut structs = source.visible_structs(analyzer)?;
        let contract = self.associated_contract(analyzer)?;
        let contract_visible = contract.visible_structs(analyzer);
        structs.extend(contract_visible);

        structs.sort();
        structs.dedup();

        self.underlying_mut(analyzer)?.cache.visible_structs = Some(structs.clone());
        Ok(structs)
    }

    /// Gets all visible contracts
    pub fn visible_contracts(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<ContractNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_contracts {
            return Ok(vis.clone());
        }

        if let Some(src) = self.maybe_associated_source(analyzer) {
            let mut cons = src.visible_contracts(analyzer)?;
            cons.sort();
            cons.dedup();

            let mut inaccessible: Vec<String> = vec![];
            inaccessible.extend(
                self.visible_structs(analyzer)?
                    .iter()
                    .map(|user_ty| user_ty.name(analyzer))
                    .collect::<Result<Vec<_>, _>>()?,
            );

            inaccessible.extend(
                self.visible_enums(analyzer)?
                    .iter()
                    .map(|user_ty| user_ty.name(analyzer))
                    .collect::<Result<Vec<_>, _>>()?,
            );

            inaccessible.extend(
                self.visible_tys(analyzer)?
                    .iter()
                    .map(|user_ty| user_ty.name(analyzer))
                    .collect::<Result<Vec<_>, _>>()?,
            );

            inaccessible.extend(
                self.visible_errors(analyzer)?
                    .iter()
                    .map(|user_ty| user_ty.name(analyzer))
                    .collect::<Result<Vec<_>, _>>()?,
            );

            let cons = cons
                .into_iter()
                .filter(|con| {
                    if let Ok(Some(name)) = con.maybe_name(analyzer) {
                        !inaccessible.contains(&name)
                    } else {
                        true
                    }
                })
                .collect::<Vec<_>>();

            self.underlying_mut(analyzer)?.cache.visible_contracts = Some(cons.clone());
            Ok(cons)
        } else {
            Ok(vec![])
        }
    }

    /// Gets all visible enums
    pub fn visible_enums(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<EnumNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_enums {
            return Ok(vis.clone());
        }

        let Some(source) = self.maybe_associated_source(analyzer) else {
            return Ok(vec![]);
        };

        let mut enums = source.visible_enums(analyzer)?;
        let contract = self.associated_contract(analyzer)?;
        let contract_visible = contract.visible_enums(analyzer);
        enums.extend(contract_visible);

        enums.sort();
        enums.dedup();

        self.underlying_mut(analyzer)?.cache.visible_enums = Some(enums.clone());
        Ok(enums)
    }

    pub fn visible_errors(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<ErrorNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_errors {
            return Ok(vis.clone());
        }

        let Some(source) = self.maybe_associated_source(analyzer) else {
            return Ok(vec![]);
        };

        let mut errors = source.visible_errors(analyzer)?;
        let contract = self.associated_contract(analyzer)?;
        let contract_visible = contract.visible_errors(analyzer);
        errors.extend(contract_visible);

        errors.sort();
        errors.dedup();

        self.underlying_mut(analyzer)?.cache.visible_errors = Some(errors.clone());
        Ok(errors)
    }

    /// Gets all visible enums
    pub fn visible_tys(
        &self,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<Vec<TyNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_tys {
            return Ok(vis.clone());
        }

        let Some(source) = self.maybe_associated_source(analyzer) else {
            return Ok(vec![]);
        };

        let mut tys = source.visible_tys(analyzer)?;
        let contract = self.associated_contract(analyzer)?;
        let contract_visible = contract.visible_tys(analyzer);
        tys.extend(contract_visible);

        tys.sort();
        tys.dedup();

        self.underlying_mut(analyzer)?.cache.visible_tys = Some(tys.clone());
        Ok(tys)
    }

    pub fn idx_is_visible(
        &self,
        node_idx: NodeIdx,
        analyzer: &mut impl AnalyzerBackend<Edge = Edge>,
    ) -> Result<bool, GraphError> {
        if self
            .visible_structs(analyzer)?
            .contains(&StructNode::from(node_idx))
        {
            return Ok(true);
        }

        if self
            .visible_contracts(analyzer)?
            .contains(&ContractNode::from(node_idx))
        {
            return Ok(true);
        }

        if self
            .visible_enums(analyzer)?
            .contains(&EnumNode::from(node_idx))
        {
            return Ok(true);
        }

        if self
            .visible_errors(analyzer)?
            .contains(&ErrorNode::from(node_idx))
        {
            return Ok(true);
        }

        return Ok(false);
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &impl GraphBackend) -> Result<FunctionNode, GraphError> {
        let underlying = self.underlying(analyzer)?;
        if let Some(fn_call) = underlying.fn_call() {
            Ok(fn_call)
        } else {
            Ok(underlying.parent_fn)
        }
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        self.associated_fn(analyzer)?.name(analyzer)
    }
}
