

impl ContextNode {
	/// Gets the associated contract for the function for the context
    pub fn associated_contract(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ContractNode, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer)
            .expect("No associated contract for context"))
    }

    /// Tries to get the associated function for the context
    pub fn maybe_associated_contract(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ContractNode>, GraphError> {
        Ok(self
            .associated_fn(analyzer)?
            .maybe_associated_contract(analyzer))
    }

    pub fn maybe_associated_source(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Option<NodeIdx> {
        let context = self.underlying(analyzer).unwrap();
        if let Some(src) = context.cache.associated_source {
            Some(src)
        } else if let Some(parent_ctx) = context.parent_ctx {
            let src = parent_ctx.maybe_associated_source(analyzer)?;
            self.underlying_mut(analyzer)
                .unwrap()
                .cache
                .associated_source = Some(src);
            Some(src)
        } else {
            let func = self.associated_fn(analyzer).unwrap();
            func.maybe_associated_source(analyzer)
        }
    }

    pub fn associated_source_unit_part(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<NodeIdx, GraphError> {
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

    /// Gets visible functions
    pub fn visible_modifiers(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
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
                    .search_children_depth(source, &Edge::Modifier, 1, 0)
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

                    if as_vec.len() > 2 {
                        println!("{}", as_vec.iter().map(|i| i.name(analyzer).unwrap()).collect::<Vec<_>>().join(", "));
                        panic!("3+ visible functions with the same name. This is invalid solidity, {as_vec:#?}")
                    } else if as_vec.len() == 2 {
                        as_vec[0].get_overriding(as_vec[1], analyzer)
                    } else {
                        Ok(*as_vec[0])
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
                .search_children_depth(source, &Edge::Modifier, 1, 0)
                .into_iter()
                .map(FunctionNode::from)
                .collect::<Vec<_>>())
        }
    }

    /// Gets visible functions
    pub fn visible_funcs(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Vec<FunctionNode>, GraphError> {
        // TODO: filter privates
        if let Some(vis) = &self.underlying(analyzer)?.cache.visible_funcs {
            return Ok(vis.clone());
        }
        if let Some(contract) = self.maybe_associated_contract(analyzer)? {
            let mut mapping = contract.linearized_functions(analyzer);
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
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Vec<FunctionNode> {
        // TODO: filter privates
        let Some(source) = self.maybe_associated_source(analyzer) else {
            return vec![];
        };
        analyzer
            .search_children_exclude_via(
                source,
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
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Vec<StructNode> {
        // TODO: filter privates
        let Some(source) = self.maybe_associated_source(analyzer) else {
            return vec![];
        };

        analyzer
            .search_children_exclude_via(source, &Edge::Struct, &[Edge::Func])
            .into_iter()
            .map(StructNode::from)
            .collect::<Vec<_>>()
    }

    /// Gets the associated function for the context
    pub fn associated_fn(&self, analyzer: &impl GraphLike) -> Result<FunctionNode, GraphError> {
        let underlying = self.underlying(analyzer)?;
        if let Some(fn_call) = underlying.fn_call {
            Ok(fn_call)
        } else if let Some(ext_fn_call) = underlying.ext_fn_call {
            Ok(ext_fn_call)
        } else {
            Ok(underlying.parent_fn)
        }
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        self.associated_fn(analyzer)?.name(analyzer)
    }
}