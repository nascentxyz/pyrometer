


#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
/// A wrapper of a node index that corresponds to a [`Context`]
pub struct ContextNode(pub usize);

impl AsDotStr for ContextNode {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        format!("Context {{ {} }}", self.path(analyzer))
    }
}

impl ContextNode {
    // pub fn called_functions(&self, analyzer: &impl GraphLike) -> Result<Vec<FunctionNode>, GraphError> {
    //     self.underlying(analyzer)?.children.iter().filter_map(|child| {
    //         match child.maybe_call()?.underlying(analyzer) {
    //             Ok(underlying) => {
    //                 match (underlying.fn_call, underlying.ext_fn_call) {
    //                     (Some(fn_call), _) => Some(Ok(fn_call)),
    //                     (_, Some(ext_fn_call)) => Some(Ok(ext_fn_call)),
    //                     (None, None) => None
    //                 }
    //             }
    //             Err(_) => None
    //         }
    //     }).collect()
    // }

    pub fn join(
        &self,
        _func: FunctionNode,
        _mapping: &BTreeMap<ContextVarNode, FunctionParamNode>,
        _analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) {
        todo!("Joining not supported yet");
        // println!("joining");
        // if let Some(body_ctx) = func.maybe_body_ctx(analyzer) {
        //     let vars: Vec<_> = body_ctx.vars(analyzer).values().map(|var| var.latest_version(analyzer)).collect();
        //     println!("vars: {vars:#?}");
        //     let replacements: Vec<(ContextVarNode, ContextVarNode)> = mapping.iter().filter_map(|(input_var, param)| {
        //         vars.iter().find(|var| var.name(analyzer).unwrap() == param.name(analyzer).unwrap()).map(|var| {
        //             (*var, *input_var)
        //         })
        //     }).collect();

        //     let mut mapping = BTreeMap::default();
        //     replacements.into_iter().for_each(|(var, replacement)| {
        //         mapping.insert(var, replacement);
        //         let mut latest = var;
        //         while let Some(next) = latest.next_version(analyzer) {
        //             latest = next;
        //             mapping.insert(latest, replacement);
        //         }
        //     });

        //     println!("mapping: {mapping:#?}");

        //     vars.iter().for_each(|var| {
        //         let mut latest = *var;
        //         let mut range = latest.range(analyzer).unwrap().unwrap();
        //         println!("var: {var:?}, depends on: {:#?}, {range:#?}", var.range_deps(analyzer));
        //         range.uncache_range_min();
        //         range.uncache_range_max();
        //         mapping.iter().for_each(|(to_replace, replacement)| {
        //             // range.filter_min_recursion((*to_replace).into(), (*replacement).into());
        //             // range.filter_max_recursion((*to_replace).into(), (*replacement).into());
        //         });
        //         latest.set_range(analyzer, range).unwrap();
        //         while let Some(next) = latest.next_version(analyzer) {
        //             latest = next;
        //             let mut range = latest.range(analyzer).unwrap().unwrap();
        //             range.uncache_range_min();
        //             range.uncache_range_max();
        //             mapping.iter().for_each(|(to_replace, replacement)| {
        //                 // range.filter_min_recursion((*to_replace).into(), (*replacement).into());
        //                 // range.filter_max_recursion((*to_replace).into(), (*replacement).into());
        //             });
        //             latest.set_range(analyzer, range).unwrap();
        //         }
        //     });

        // } else {
        //     // need to process the function
        // }
    }

    pub fn is_ext_fn(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.ext_fn_call.is_some())
    }

    pub fn add_var(
        &self,
        var: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let name = var.name(analyzer)?;
        let vars = &mut self.underlying_mut(analyzer)?.cache.vars;
        vars.insert(name, var);
        Ok(())
    }

    pub fn first_ancestor(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ContextNode, GraphError> {
        if let Some(first_ancestor) = self.underlying(analyzer)?.cache.first_ancestor {
            Ok(first_ancestor)
        } else if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            let first = parent.first_ancestor(analyzer)?;
            self.underlying_mut(analyzer)?.cache.first_ancestor = Some(first);
            Ok(first)
        } else {
            Ok(*self)
        }
    }

    pub fn total_width(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<usize, GraphError> {
        self.first_ancestor(analyzer)?
            .number_of_live_edges(analyzer)
    }

    pub fn unchecked(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.unchecked)
    }

    pub fn set_unchecked(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.unchecked = true;
        Ok(())
    }

    pub fn unset_unchecked(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.unchecked = false;
        Ok(())
    }

    pub fn push_tmp_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        underlying_mut.tmp_expr.push(Some(expr_ret));
        Ok(())
    }

    pub fn append_tmp_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        match underlying_mut.tmp_expr.pop() {
            Some(Some(s @ ExprRet::Single(_))) => {
                underlying_mut
                    .tmp_expr
                    .push(Some(ExprRet::Multi(vec![s, expr_ret])));
            }
            Some(Some(s @ ExprRet::SingleLiteral(_))) => {
                underlying_mut
                    .tmp_expr
                    .push(Some(ExprRet::Multi(vec![s, expr_ret])));
            }
            Some(Some(ExprRet::Multi(ref mut inner))) => {
                inner.push(expr_ret);
                underlying_mut
                    .tmp_expr
                    .push(Some(ExprRet::Multi(inner.to_vec())));
            }
            Some(Some(s @ ExprRet::Null)) => {
                underlying_mut
                    .tmp_expr
                    .push(Some(ExprRet::Multi(vec![s, expr_ret])));
            }
            Some(Some(ExprRet::CtxKilled(kind))) => {
                underlying_mut.tmp_expr = vec![Some(ExprRet::CtxKilled(kind))];
                underlying_mut.expr_ret_stack = vec![ExprRet::CtxKilled(kind)];
            }
            _ => {
                underlying_mut.tmp_expr.push(Some(expr_ret));
            }
        }
        Ok(())
    }

    pub fn pop_tmp_expr(
        &self,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        if let Some(Some(expr)) = underlying_mut.tmp_expr.pop() {
            Ok(Some(self.maybe_move_expr(expr, loc, analyzer)?))
        } else {
            Ok(None)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn push_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        tracing::trace!(
            "pushing: {}, existing: {:?}, path: {}",
            expr_ret.debug_str(analyzer),
            self.underlying(analyzer)?
                .expr_ret_stack
                .iter()
                .map(|i| i.debug_str(analyzer))
                .collect::<Vec<_>>(),
            self.path(analyzer)
        );
        let underlying_mut = self.underlying_mut(analyzer)?;
        underlying_mut.expr_ret_stack.push(expr_ret);
        Ok(())
    }

    pub fn maybe_move_expr(
        &self,
        expr: ExprRet,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ExprRet, GraphError> {
        match expr {
            ExprRet::SingleLiteral(var) => Ok(ExprRet::SingleLiteral(
                self.maybe_move_var(var.into(), loc, analyzer)?.into(),
            )),
            ExprRet::Single(var) => Ok(ExprRet::Single(
                self.maybe_move_var(var.into(), loc, analyzer)?.into(),
            )),
            ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                inner
                    .iter()
                    .map(|i| self.maybe_move_expr(i.clone(), loc, analyzer))
                    .collect::<Result<_, _>>()?,
            )),
            e => Ok(e),
        }
    }

    pub fn maybe_move_var(
        &self,
        var: ContextVarNode,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<ContextVarNode, GraphError> {
        if let Some(ctx) = var.maybe_ctx(analyzer) {
            if ctx != *self {
                let mut new_cvar = var.latest_version(analyzer).underlying(analyzer)?.clone();
                new_cvar.loc = Some(loc);

                let new_cvarnode = analyzer.add_node(Node::ContextVar(new_cvar));
                analyzer.add_edge(new_cvarnode, *self, Edge::Context(ContextEdge::Variable));
                analyzer.add_edge(
                    new_cvarnode,
                    var.0,
                    Edge::Context(ContextEdge::InheritedVariable),
                );
                Ok(new_cvarnode.into())
            } else {
                Ok(var)
            }
        } else {
            Ok(var)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn pop_expr(
        &self,
        _loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        tracing::trace!("popping var from: {}", self.path(analyzer));
        let underlying_mut = self.underlying_mut(analyzer)?;

        let new: Vec<ExprRet> = Vec::with_capacity(5);

        let old = std::mem::replace(&mut underlying_mut.expr_ret_stack, new);
        if old.is_empty() {
            Ok(None)
        } else {
            Ok(Some(ExprRet::Multi(old)))
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    pub fn pop_expr_latest(
        &self,
        loc: Loc,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        if let Some(elem) = underlying_mut.expr_ret_stack.pop() {
            tracing::trace!(
                "popping var {} from: {}",
                elem.debug_str(analyzer),
                self.path(analyzer)
            );
            Ok(Some(self.maybe_move_expr(elem, loc, analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn vars_assigned_from_fn_ret(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        self.local_vars(analyzer)
            .iter()
            .flat_map(|(_name, var)| var.return_assignments(analyzer))
            .collect()
    }

    pub fn vars_assigned_from_ext_fn_ret(&self, analyzer: &impl GraphLike) -> Vec<ContextVarNode> {
        self.local_vars(analyzer)
            .iter()
            .flat_map(|(_name, var)| var.ext_return_assignments(analyzer))
            .collect()
    }

    pub fn depth(&self, analyzer: &impl GraphLike) -> usize {
        self.underlying(analyzer).unwrap().depth
    }

    /// The path of the underlying context
    pub fn path(&self, analyzer: &impl GraphLike) -> String {
        self.underlying(analyzer).unwrap().path.clone()
    }

    /// *All* subcontexts (including subcontexts of subcontexts, recursively)
    pub fn subcontexts(&self, analyzer: &impl GraphLike) -> Vec<ContextNode> {
        let underlying = self.underlying(analyzer).unwrap();
        match underlying.child {
            Some(CallFork::Call(c)) => vec![c],
            Some(CallFork::Fork(w1, w2)) => vec![w1, w2],
            None => vec![],
        }
    }

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
            return Err(GraphError::NodeConfusion("Expected context to have an associated source but didnt".to_string()))
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
                return Err(GraphError::NodeConfusion("Expected context to have an associated source but didnt".to_string()));
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
            return vec![]
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
            return vec![]
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

    /// Checks whether a function is external to the current context
    pub fn is_fn_ext(
        &self,
        fn_node: FunctionNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<bool, GraphError> {
        match fn_node.maybe_associated_contract(analyzer) {
            None => Ok(false),
            Some(fn_ctrt) => {
                if let Some(self_ctrt) = self
                    .associated_fn(analyzer)?
                    .maybe_associated_contract(analyzer)
                {
                    Ok(Some(self_ctrt) != Some(fn_ctrt)
                        && !self_ctrt
                            .underlying(analyzer)?
                            .inherits
                            .iter()
                            .any(|inherited| *inherited == fn_ctrt))
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Gets the associated function name for the context
    pub fn associated_fn_name(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        self.associated_fn(analyzer)?.name(analyzer)
    }

    /// Gets a mutable reference to the underlying context in the graph
    pub fn underlying_mut<'a>(
        &self,
        analyzer: &'a mut (impl GraphLike + AnalyzerLike),
    ) -> Result<&'a mut Context, GraphError> {
        match analyzer.node_mut(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets an immutable reference to the underlying context in the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Context, GraphError> {
        match analyzer.node(*self) {
            Node::Context(c) => Ok(c),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Context but it was: {e:?}"
            ))),
        }
    }

    /// Gets a variable by name in the context
    pub fn var_by_name(&self, analyzer: &impl GraphLike, name: &str) -> Option<ContextVarNode> {
        self.underlying(analyzer)
            .unwrap()
            .cache
            .vars
            .get(name)
            .copied()
    }

    pub fn var_by_name_or_recurse(
        &self,
        analyzer: &impl GraphLike,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = self.var_by_name(analyzer, name) {
            Ok(Some(var))
        } else if let Some(parent) = self.ancestor_in_fn(analyzer, self.associated_fn(analyzer)?)? {
            parent.var_by_name_or_recurse(analyzer, name)
        } else {
            Ok(None)
        }
    }

    pub fn ancestor_in_fn(
        &self,
        analyzer: &impl GraphLike,
        associated_fn: FunctionNode,
    ) -> Result<Option<ContextNode>, GraphError> {
        if let Some(ret) = self.underlying(analyzer)?.returning_ctx {
            if ret.associated_fn(analyzer)? == associated_fn {
                return Ok(Some(ret));
            }
        }

        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            if parent.associated_fn(analyzer)? == associated_fn {
                Ok(Some(parent))
            } else if let Some(mod_state) = &parent.underlying(analyzer)?.modifier_state {
                if mod_state.parent_fn == associated_fn {
                    Ok(Some(parent))
                } else {
                    parent.ancestor_in_fn(analyzer, associated_fn)
                }
            } else {
                parent.ancestor_in_fn(analyzer, associated_fn)
            }
        } else {
            Ok(None)
        }
    }

    /// Gets all variables associated with a context
    pub fn vars<'a>(&self, analyzer: &'a impl GraphLike) -> &'a BTreeMap<String, ContextVarNode> {
        &self.underlying(analyzer).unwrap().cache.vars
    }

    /// Gets all variables associated with a context
    pub fn local_vars<'a>(
        &self,
        analyzer: &'a impl GraphLike,
    ) -> &'a BTreeMap<String, ContextVarNode> {
        self.vars(analyzer)
    }

    /// Gets the latest version of a variable associated with a context
    pub fn latest_var_by_name(
        &self,
        analyzer: &impl GraphLike,
        name: &str,
    ) -> Option<ContextVarNode> {
        self.var_by_name(analyzer, name)
            .map(|var| var.latest_version(analyzer))
    }

    /// Reads the current temporary counter and increments the counter
    pub fn new_tmp(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<usize, GraphError> {
        let context = self.underlying_mut(analyzer)?;
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        Ok(ret)
    }

    /// Returns all forks associated with the context
    pub fn calls(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        let descendents = self.descendents(analyzer)?;
        Ok(descendents
            .into_iter()
            .filter_map(|c| c.maybe_call())
            .collect())
    }

    /// Returns all forks associated with the context
    // pub fn forks(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
    // todo!()
    // let descendents = self.descendents(analyzer)?;
    // Ok(descendents.into_iter().filter_map(|c| c.maybe_fork()).collect())
    // }

    // /// Returns all *live* forks associated with the context
    // pub fn live_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
    //     let forks = self.forks(analyzer)?;
    //     let mut live = vec![];
    //     for fork in forks {
    //         if !fork.is_ended(analyzer)? {
    //             live.push(fork);
    //         }
    //     }
    //     Ok(live)
    // }

    /// Returns tail contexts associated with the context
    pub fn live_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.live_edges(analyzer)?;
                    if call_edges.is_empty() && !call.is_ended(analyzer)? {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.live_edges(analyzer)?;
                    if fork_edges.is_empty() && !w1.is_ended(analyzer)? {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.live_edges(analyzer)?;
                    if fork_edges.is_empty() && !w2.is_ended(analyzer)? {
                        lineage.push(w2)
                    } else {
                        lineage.extend(fork_edges);
                    }
                }
            }
            Ok(lineage)
        } else {
            Ok(vec![])
        }
    }

    pub fn reverted_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.reverted_edges(analyzer)?;
                    if call_edges.is_empty() && call.is_killed(analyzer)? {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.reverted_edges(analyzer)?;
                    if fork_edges.is_empty() && w1.is_killed(analyzer)? {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.reverted_edges(analyzer)?;
                    if fork_edges.is_empty() && w2.is_killed(analyzer)? {
                        lineage.push(w2)
                    } else {
                        lineage.extend(fork_edges);
                    }
                }
            }
            Ok(lineage)
        } else {
            Ok(vec![])
        }
    }

    pub fn number_of_live_edges(&self, analyzer: &impl GraphLike) -> Result<usize, GraphError> {
        Ok(self.underlying(analyzer)?.number_of_live_edges)
        // if let Some(child) = self.underlying(analyzer)?.child {
        //     let mut edges = 0;
        //     match child {
        //         CallFork::Call(call) => {
        //             let call_edges = call.number_of_live_edges(analyzer)?;
        //             if call_edges == 0 && !call.is_ended(analyzer)? {
        //                 edges += 1;
        //             } else {
        //                 edges += call_edges;
        //             }
        //         }
        //         CallFork::Fork(w1, w2) => {
        //             let fork_edges = w1.number_of_live_edges(analyzer)?;
        //             if fork_edges == 0 && !w1.is_ended(analyzer)? {
        //                 edges += 1;
        //             } else {
        //                 edges += fork_edges;
        //             }

        //             let fork_edges = w2.number_of_live_edges(analyzer)?;
        //             if fork_edges == 0 && !w2.is_ended(analyzer)? {
        //                 edges += 1;
        //             } else {
        //                 edges += fork_edges;
        //             }
        //         }
        //     }
        //     Ok(edges)
        // } else {
        //     Ok(0)
        // }
    }

    /// Returns tail contexts associated with the context
    pub fn all_edges(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut lineage = vec![];
            match child {
                CallFork::Call(call) => {
                    let call_edges = call.all_edges(analyzer)?;
                    if call_edges.is_empty() {
                        lineage.push(call)
                    } else {
                        lineage.extend(call_edges);
                    }
                }
                CallFork::Fork(w1, w2) => {
                    let fork_edges = w1.all_edges(analyzer)?;
                    if fork_edges.is_empty() {
                        lineage.push(w1)
                    } else {
                        lineage.extend(fork_edges);
                    }

                    let fork_edges = w2.all_edges(analyzer)?;
                    if fork_edges.is_empty() {
                        lineage.push(w2)
                    } else {
                        lineage.extend(fork_edges);
                    }
                }
            }
            Ok(lineage)
        } else {
            Ok(vec![])
        }
    }

    pub fn descendents(&self, analyzer: &impl GraphLike) -> Result<Vec<CallFork>, GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            let mut descendents = vec![child];
            match child {
                CallFork::Call(c) => descendents.extend(c.descendents(analyzer)?),
                CallFork::Fork(w1, w2) => {
                    descendents.extend(w1.descendents(analyzer)?);
                    descendents.extend(w2.descendents(analyzer)?);
                }
            }
            Ok(descendents)
        } else {
            Ok(vec![])
        }
    }

    /// Adds a fork to the context
    pub fn set_child_fork(
        &self,
        w1: ContextNode,
        w2: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        assert!(matches!(analyzer.node(w1), Node::Context(_)));
        assert!(matches!(analyzer.node(w2), Node::Context(_)));
        assert!(*self != w1 && *self != w2, "Tried to set child to self");
        let context = self.underlying_mut(analyzer)?;
        if !context.set_child_fork(w1, w2) {
            let child_str = match context.child {
                Some(CallFork::Fork(w1, w2)) => {
                    format!("fork {{ {}, {} }}", w1.path(analyzer), w2.path(analyzer))
                }
                Some(CallFork::Call(call)) => format!("call {{ {} }}", call.path(analyzer)),
                None => unreachable!(),
            };
            Err(GraphError::ChildRedefinition(format!(
                "This is a bug. Tried to redefine a child context, parent:\n{}, current child:\n{},\nnew child: Fork({}, {})",
                self.path(analyzer),
                child_str,
                w1.path(analyzer),
                w2.path(analyzer),
            )))
        } else {
            Ok(())
        }
    }

    /// Adds a child to the context
    pub fn set_child_call(
        &self,
        call: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        assert!(matches!(analyzer.node(call), Node::Context(_)));
        assert!(*self != call, "Tried to set child to self");
        let context = self.underlying_mut(analyzer)?;
        if !context.set_child_call(call) {
            let child_str = match context.child {
                Some(CallFork::Fork(w1, w2)) => {
                    format!("fork {{ {}, {} }}", w1.path(analyzer), w2.path(analyzer))
                }
                Some(CallFork::Call(call)) => format!("call {{ {} }}", call.path(analyzer)),
                None => unreachable!(),
            };
            tracing::trace!("Error setting child as a call");
            Err(GraphError::ChildRedefinition(format!(
                "This is a bug. Tried to redefine a child context, parent: {}, current child: {}, new child: {}",
                self.path(analyzer),
                child_str,
                call.path(analyzer)
            )
            ))
        } else {
            Ok(())
        }
    }

    pub fn delete_child(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if let Some(child) = self.underlying(analyzer)?.child {
            match child {
                CallFork::Fork(w1, w2) => {
                    w1.propogate_end(analyzer)?;
                    w2.propogate_end(analyzer)?;
                }
                CallFork::Call(c) => {
                    c.propogate_end(analyzer)?;
                }
            }
        }
        let context = self.underlying_mut(analyzer)?;
        context.delete_child();
        Ok(())
    }

    /// Kills the context by denoting it as killed. Recurses up the contexts and kills
    /// parent contexts if all subcontexts of that context are killed
    pub fn kill(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        kill_loc: Loc,
        kill_kind: KilledKind,
    ) -> Result<(), GraphError> {
        tracing::trace!("killing: {}", self.path(analyzer));
        if let Some(child) = self.underlying(analyzer)?.child {
            match child {
                CallFork::Call(call) => {
                    if !call.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }
                    call.kill(analyzer, kill_loc, kill_kind)?;
                }
                CallFork::Fork(w1, w2) => {
                    if !w1.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }

                    if !w2.underlying(analyzer)?.ret.is_empty() {
                        return Ok(());
                    }

                    w1.kill(analyzer, kill_loc, kill_kind)?;
                    w2.kill(analyzer, kill_loc, kill_kind)?;
                }
            }
        }

        let context = self.underlying_mut(analyzer)?;
        let parent = context.parent_ctx;
        if context.killed.is_none() {
            context.killed = Some((kill_loc, kill_kind));
        }

        if let Some(parent_ctx) = parent {
            parent_ctx.end_if_all_forks_ended(analyzer, kill_loc, kill_kind)?;
        }

        self.propogate_end(analyzer)?;

        Ok(())
    }

    /// Kills if and only if all subcontexts are killed
    pub fn end_if_all_forks_ended(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        kill_loc: Loc,
        kill_kind: KilledKind,
    ) -> Result<(), GraphError> {
        let all_edges = self.all_edges(analyzer)?;
        let reverted_edges = self.reverted_edges(analyzer)?;
        if reverted_edges.len() == all_edges.len() {
            tracing::trace!("killing recursively: {}", self.path(analyzer));
            let context = self.underlying_mut(analyzer)?;
            if context.ret.is_empty() {
                if context.killed.is_none() {
                    context.killed = Some((kill_loc, kill_kind));
                }
                if let Some(parent_ctx) = context.parent_ctx {
                    parent_ctx.end_if_all_forks_ended(analyzer, kill_loc, kill_kind)?;
                }
            }
        }
        Ok(())
    }

    /// Gets parent list
    pub fn parent_list(&self, analyzer: &impl GraphLike) -> Result<Vec<ContextNode>, GraphError> {
        let context = self.underlying(analyzer)?;
        let mut parents = vec![];
        if let Some(parent_ctx) = context.parent_ctx {
            parents.push(parent_ctx);
            parents.extend(parent_ctx.parent_list(analyzer)?);
        }
        Ok(parents)
    }

    pub fn recursive_calls(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        // Ok(
        let calls = self.calls(analyzer)?;
        Ok(calls
            .iter()
            .flat_map(|call| {
                let mut inner_calls = call.recursive_calls(analyzer).unwrap();
                inner_calls.insert(0, *call);
                inner_calls
            })
            .collect::<Vec<ContextNode>>())
    }

    /// Gets the lineage for a context
    /// A lineage is of the form `[ancestor N, .. , ancestor0, SELF, call0, .., call N]`. It
    /// gives the user a full picture of control flow
    pub fn lineage(
        &self,
        _analyzer: &impl GraphLike,
        _entry: bool,
    ) -> Result<Vec<ContextNode>, GraphError> {
        todo!()
    }

    pub fn terminal_child_list(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<ContextNode>, GraphError> {
        let calls = self.calls(analyzer)?;
        if calls.is_empty() {
            Ok(vec![*self])
        } else {
            let mut children = vec![];

            for child in calls.into_iter() {
                children.extend(child.terminal_child_list(analyzer)?)
            }
            Ok(children)
        }
    }

    /// Returns whether the context is killed
    pub fn is_killed(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.killed.is_some())
    }

    /// Returns whether the context is killed
    pub fn is_ended(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.child.is_some() || underlying.killed.is_some() || !underlying.ret.is_empty())
    }

    pub fn killed_or_ret(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.killed.is_some()
            || (!underlying.ret.is_empty() && underlying.modifier_state.is_none()))
    }

    /// Returns an option to where the context was killed
    pub fn killed_loc(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<(Loc, KilledKind)>, GraphError> {
        Ok(self.underlying(analyzer)?.killed)
    }

    /// Returns a map of variable dependencies for this context
    pub fn ctx_deps(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<BTreeMap<String, ContextVarNode>, GraphError> {
        Ok(self.underlying(analyzer)?.ctx_deps.clone())
    }

    /// Returns a vector of variable dependencies for this context
    pub fn add_ctx_dep(
        &self,
        dep: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        tracing::trace!("Adding ctx dependency: {}", dep.display_name(analyzer)?);
        if dep.is_symbolic(analyzer)? {
            let dep_name = dep.name(analyzer)?;
            let underlying = self.underlying_mut(analyzer)?;
            underlying.ctx_deps.insert(dep_name, dep);
        }
        Ok(())
    }

    pub fn add_return_node(
        &self,
        ret_stmt_loc: Loc,
        ret: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.ret.push((ret_stmt_loc, ret));
        self.propogate_end(analyzer)?;
        Ok(())
    }

    pub fn propogate_end(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        let underlying = &mut self.underlying_mut(analyzer)?;
        let curr_live = underlying.number_of_live_edges;
        underlying.number_of_live_edges = 0;
        if let Some(parent) = self.underlying(analyzer)?.parent_ctx {
            let live_edges = &mut parent.underlying_mut(analyzer)?.number_of_live_edges;
            *live_edges = live_edges.saturating_sub(1 + curr_live);
            parent.propogate_end(analyzer)?;
        }
        Ok(())
    }

    pub fn return_nodes(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Vec<(Loc, ContextVarNode)>, GraphError> {
        Ok(self.underlying(analyzer)?.ret.clone())
    }

    pub fn as_string(&mut self) -> String {
        "Context".to_string()
    }

    pub fn deps_dag(&self, g: &impl GraphLike) -> Result<(), GraphError> {
        let deps = self.ctx_deps(g)?;
        #[derive(Debug, Copy, Clone)]
        pub enum DepEdge {
            Lhs,
            Rhs,
        }

        let mut gr: petgraph::Graph<NodeIdx, DepEdge, petgraph::Directed, usize> =
            petgraph::Graph::default();
        deps.iter().try_for_each(|(_, dep)| {
            let mapping = dep.graph_dependent_on(g)?;
            mapping.into_iter().for_each(|(k, tmp)| {
                let top = gr.add_node(k.into());
                let lhs = gr.add_node(tmp.lhs.into());
                gr.add_edge(top, lhs, DepEdge::Lhs);
                if let Some(rhs) = tmp.rhs {
                    let rhs = gr.add_node(rhs.into());
                    gr.add_edge(top, rhs, DepEdge::Rhs);
                }
            });
            Ok(())
        })?;

        let mut dot_str = Vec::new();
        let raw_start_str = r##"digraph G {
    node [shape=box, style="filled, rounded", color="#565f89", fontcolor="#d5daf0", fontname="Helvetica", fillcolor="#24283b"];
    edge [color="#414868", fontcolor="#c0caf5", fontname="Helvetica"];
    bgcolor="#1a1b26";"##;
        dot_str.push(raw_start_str.to_string());
        let nodes_and_edges_str = format!(
            "{:?}",
            Dot::with_attr_getters(
                &gr,
                &[
                    petgraph::dot::Config::GraphContentOnly,
                    petgraph::dot::Config::NodeNoLabel,
                    petgraph::dot::Config::EdgeNoLabel
                ],
                &|_graph, edge_ref| {
                    let e = edge_ref.weight();
                    format!("label = \"{e:?}\"")
                },
                &|_graph, (idx, node_ref)| {
                    let inner = match g.node(*node_ref) {
                        Node::ContextVar(cvar) => {
                            let range_str = if let Some(r) = cvar.ty.ref_range(g).unwrap() {
                                r.as_dot_str(g)
                                // format!("[{}, {}]", r.min.eval(self).to_range_string(self).s, r.max.eval(self).to_range_string(self).s)
                            } else {
                                "".to_string()
                            };

                            format!(
                                "{} -- {} -- range: {}",
                                cvar.display_name,
                                cvar.ty.as_string(g).unwrap(),
                                range_str
                            )
                        }
                        _ => as_dot_str(idx, g),
                    };
                    format!(
                        "label = \"{}\", color = \"{}\"",
                        inner.replace('\"', "\'"),
                        g.node(*node_ref).dot_str_color()
                    )
                }
            )
        );
        dot_str.push(nodes_and_edges_str);
        let raw_end_str = r#"}"#;
        dot_str.push(raw_end_str.to_string());
        let dot_str = dot_str.join("\n");

        println!("{dot_str}");
        use std::env::temp_dir;
        use std::fs;
        use std::io::Write;
        use std::process::Command;
        let mut dir = temp_dir();
        let file_name = "dot.dot";
        dir.push(file_name);

        let mut file = fs::File::create(dir.clone()).unwrap();
        file.write_all(dot_str.as_bytes()).unwrap();
        Command::new("dot")
            .arg("-Tsvg")
            .arg(dir)
            .arg("-o")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
        Command::new("open")
            .arg("dot.svg")
            .output()
            .expect("failed to execute process");
        Ok(())
    }
}

impl From<ContextNode> for NodeIdx {
    fn from(val: ContextNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for ContextNode {
    fn from(idx: NodeIdx) -> Self {
        ContextNode(idx.index())
    }
}