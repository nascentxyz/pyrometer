use crate::{
    nodes::{ContextNode, ContextVarNode, EnvCtxNode, ExprRet, VarNode},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, TypeNode,
};
use petgraph::Direction;
use shared::GraphError;

use petgraph::visit::EdgeRef;
use solang_parser::pt::Loc;

use std::collections::BTreeMap;

impl ContextNode {
    pub fn input_variables(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        self.vars(analyzer)
            .iter()
            .filter_map(|(_, var)| {
                if var.is_func_input(analyzer) {
                    Some(var.first_version(analyzer))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Debug print the stack
    pub fn debug_expr_stack_str(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        let underlying_mut = self.underlying(analyzer)?;
        Ok(format!(
            "{:#?}",
            underlying_mut
                .expr_ret_stack
                .iter()
                .rev()
                .enumerate()
                .map(|(i, elem)| format!("{i}. {}", elem.debug_str(analyzer)))
                .collect::<Vec<_>>()
        ))
    }

    pub fn debug_expr_stack(&self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        println!("{}", self.debug_expr_stack_str(analyzer)?);
        Ok(())
    }

    /// Add a variable to this context
    pub fn add_var(
        &self,
        var: ContextVarNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        // var.cache_range(analyzer)?;
        if var.is_storage(analyzer)? {
            let name = var.name(analyzer)?;
            let vars = &mut self.underlying_mut(analyzer)?.cache.storage_vars;
            vars.insert(name, var);
        }

        if var.underlying(analyzer)?.is_tmp {
            let name = var.display_name(analyzer)?;
            let vars = &mut self.underlying_mut(analyzer)?.cache.tmp_vars;
            vars.insert(name, var);
            Ok(())
        } else {
            let name = var.name(analyzer)?;
            let vars = &mut self.underlying_mut(analyzer)?.cache.vars;
            vars.insert(name, var);
            Ok(())
        }
    }

    /// Returns whether the context's cache contains a variable (by name)
    pub fn contains_var(
        &self,
        var_name: &str,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.cache.vars.contains_key(var_name))
    }

    /// Gets a variable by name in the context
    pub fn var_by_name(&self, analyzer: &impl GraphBackend, name: &str) -> Option<ContextVarNode> {
        self.underlying(analyzer)
            .unwrap()
            .cache
            .vars
            .get(name)
            .copied()
    }

    pub fn tmp_var_by_name(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Option<ContextVarNode> {
        self.underlying(analyzer)
            .unwrap()
            .cache
            .tmp_vars
            .get(name)
            .copied()
    }

    pub fn env_or_recurse(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Option<EnvCtxNode>, GraphError> {
        if let Some(env) = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .find(|e| matches!(e.weight(), Edge::Context(ContextEdge::Env)))
            .map(|e| e.source())
        {
            return Ok(Some(env.into()));
        }

        if let Some(parent) = self.ancestor_in_call(analyzer)? {
            if let Some(in_parent) = parent.env_or_recurse(analyzer)? {
                Ok(Some(in_parent))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    pub fn storage_var_by_name(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Option<ContextVarNode> {
        self.underlying(analyzer)
            .unwrap()
            .cache
            .storage_vars
            .get(name)
            .copied()
    }

    /// Gets a variable by name or recurses up the relevant scopes/contexts until it is found
    pub fn var_by_name_or_recurse(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = self.var_by_name(analyzer, name) {
            return Ok(Some(var));
        }

        if let Some(parent) = self.ancestor_in_fn(analyzer, self.associated_fn(analyzer)?)? {
            if let Some(in_parent) = parent.var_by_name_or_recurse(analyzer, name)? {
                return Ok(Some(in_parent));
            }
        }

        if let Some(parent) = self.underlying(analyzer)?.continuation_of() {
            parent.var_by_name_or_recurse(analyzer, name)
        } else {
            Ok(None)
        }
    }

    pub fn storage_var_by_name_or_recurse(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = self.storage_var_by_name(analyzer, name) {
            return Ok(Some(var));
        }

        let relevant_contract = self.contract_id(analyzer)?;
        let mut next_parent = self.underlying(analyzer)?.parent_ctx();
        while let Some(parent) = next_parent {
            let parent_contract = parent.contract_id(analyzer)?;
            if parent_contract == relevant_contract {
                if let Some(in_parent) = parent.storage_var_by_name(analyzer, name) {
                    return Ok(Some(in_parent.latest_version(analyzer)));
                }
            }

            next_parent = parent.underlying(analyzer)?.parent_ctx();
        }

        Ok(None)
    }

    /// Gets a variable by name or recurses up the relevant scopes/contexts until it is found
    pub fn struct_field_access_by_name_recurse(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        loc: Loc,
        full_name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        let split = full_name.split('.').collect::<Vec<_>>();
        if split.len() < 2 {
            return Ok(None);
        }

        let member_name = split[0..=split.len() - 2].join(".");
        let field_name = split.last().unwrap();

        // get the member
        let Some(member) = self.var_by_name_or_recurse(analyzer, &member_name)? else {
            return Ok(None);
        };

        // maybe move var into this context
        let member = self.maybe_move_var(member, loc, analyzer)?;
        let fields = member.fielded_to_fields(analyzer)?;
        let field = fields.into_iter().find(|field| {
            let full_name = field.name(analyzer).unwrap();
            let target_field_name = full_name.split('.').last().unwrap();
            *field_name == target_field_name
        });

        Ok(field)
    }

    /// Gets all storage variables associated with a context
    pub fn storage_vars(&self, analyzer: &impl AnalyzerBackend) -> Vec<ContextVarNode> {
        self.underlying(analyzer)
            .unwrap()
            .cache
            .storage_vars
            .values()
            .cloned()
            .collect()
    }

    pub fn contract_vars_referenced(&self, analyzer: &impl AnalyzerBackend) -> Vec<VarNode> {
        // let mut storage_vars = self.storage_vars(analyzer);
        let all_vars = self.all_vars(analyzer);
        let all_contract_vars = all_vars
            .into_iter()
            .filter_map(|var| {
                if analyzer
                    .graph()
                    .edges_directed(var.1 .0.into(), petgraph::Direction::Outgoing)
                    .any(|edge| {
                        matches!(edge.weight(), Edge::Context(ContextEdge::ContractVariable))
                    })
                {
                    Some(var.1)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        all_contract_vars
            .iter()
            .filter_map(|var| {
                let name = var.name(analyzer).unwrap();
                Some(
                    analyzer
                        .user_types()
                        .get(&name)?
                        .iter()
                        .filter_map(|idx| match analyzer.node(*idx) {
                            Node::Var(_) => Some(VarNode::from(*idx)),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                )
            })
            .flatten()
            .collect()
    }

    pub fn usertype_vars_referenced(&self, analyzer: &impl AnalyzerBackend) -> Vec<TypeNode> {
        let vars = self.all_vars(analyzer);
        vars.iter()
            .filter_map(|(_, var)| var.maybe_usertype(analyzer).ok())
            .flatten()
            .collect()
    }

    pub fn contract_vars_referenced_global(&self, analyzer: &impl AnalyzerBackend) -> Vec<VarNode> {
        let mut reffed_storage = self.contract_vars_referenced(analyzer);
        analyzer
            .graph()
            .edges_directed(self.0.into(), petgraph::Direction::Incoming)
            .filter(|edge| matches!(edge.weight(), Edge::Context(ContextEdge::Continue(_))))
            .map(|edge| ContextNode::from(edge.source()))
            .for_each(|cont| {
                reffed_storage.extend(cont.contract_vars_referenced_global(analyzer));
            });

        reffed_storage.sort_by(|a, b| a.0.cmp(&b.0));
        reffed_storage.dedup();
        reffed_storage
    }

    pub fn usertype_vars_referenced_global(
        &self,
        analyzer: &impl AnalyzerBackend,
    ) -> Vec<TypeNode> {
        let mut reffed_usertypes = self.usertype_vars_referenced(analyzer);
        analyzer
            .graph()
            .edges_directed(self.0.into(), petgraph::Direction::Incoming)
            .filter(|edge| matches!(edge.weight(), Edge::Context(ContextEdge::Continue(_))))
            .map(|edge| ContextNode::from(edge.source()))
            .for_each(|cont| {
                reffed_usertypes.extend(cont.usertype_vars_referenced_global(analyzer));
            });

        reffed_usertypes.sort();
        reffed_usertypes.dedup();
        reffed_usertypes
    }

    /// Gets all variables associated with a context
    pub fn vars<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> &'a BTreeMap<String, ContextVarNode> {
        &self.underlying(analyzer).unwrap().cache.vars
    }

    /// Gets all variables associated with a context
    pub fn all_vars(&self, analyzer: &impl GraphBackend) -> BTreeMap<String, ContextVarNode> {
        analyzer
            .graph()
            .edges_directed(self.0.into(), petgraph::Direction::Incoming)
            .filter(|edge| matches!(edge.weight(), Edge::Context(ContextEdge::Variable)))
            .map(|edge| ContextVarNode::from(edge.source()))
            .map(|cvar| (cvar.name(analyzer).unwrap(), cvar))
            .collect()
    }

    /// Gets all variables associated with a context
    pub fn local_vars<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> &'a BTreeMap<String, ContextVarNode> {
        self.vars(analyzer)
    }

    /// Gets the latest version of a variable associated with a context
    pub fn latest_var_by_name(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Option<ContextVarNode> {
        self.var_by_name(analyzer, name)
            .map(|var| var.latest_version(analyzer))
    }

    /// Reads the current temporary counter and increments the counter
    pub fn new_tmp(&self, analyzer: &mut impl AnalyzerBackend) -> Result<usize, GraphError> {
        let context = self.underlying_mut(analyzer)?;
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        Ok(ret)
    }

    pub fn kill_if_ret_killed(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        loc: Loc,
    ) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        if let Some(killed_ret) = underlying
            .expr_ret_stack
            .iter()
            .find(|ret| ret.has_killed())
        {
            self.kill(analyzer, loc, killed_ret.killed_kind().unwrap())?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Pushes an ExprRet to the stack
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn push_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut impl AnalyzerBackend,
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

    /// May move the inner variables of an ExprRet from an old context to this context
    pub fn maybe_move_expr(
        &self,
        expr: ExprRet,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ExprRet, GraphError> {
        tracing::trace!("moving expr to {}", self.path(analyzer));
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

    pub fn recursive_move_struct_field(
        parent: ContextVarNode,
        field: ContextVarNode,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let mut new_cvar = field.latest_version(analyzer).underlying(analyzer)?.clone();
        new_cvar.loc = Some(loc);

        let new_cvarnode = ContextVarNode::from(analyzer.add_node(Node::ContextVar(new_cvar)));

        analyzer.add_edge(
            new_cvarnode.0,
            parent.0,
            Edge::Context(ContextEdge::AttrAccess("field")),
        );

        let sub_fields = field.fielded_to_fields(analyzer)?;
        sub_fields.iter().try_for_each(|sub_field| {
            Self::recursive_move_struct_field(new_cvarnode, *sub_field, loc, analyzer)
        })
    }

    /// May move the variable from an old context to this context
    pub fn maybe_move_var(
        &self,
        var: ContextVarNode,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ContextVarNode, GraphError> {
        if let Ok(name) = var.name(analyzer) {
            if let Some(ret_var) = self.latest_var_by_name(analyzer, &name) {
                return Ok(ret_var);
            }
        }

        let var = var.latest_version(analyzer);
        if let Some(ctx) = var.maybe_ctx(analyzer) {
            if ctx != *self {
                tracing::trace!(
                    "moving var {}from {} to {}",
                    if let Ok(name) = var.display_name(analyzer) {
                        format!("{name} ")
                    } else {
                        "".to_string()
                    },
                    ctx.path(analyzer),
                    self.path(analyzer)
                );
                let mut new_cvar = var.latest_version(analyzer).underlying(analyzer)?.clone();
                new_cvar.loc = Some(loc);

                let new_cvarnode =
                    ContextVarNode::from(analyzer.add_node(Node::ContextVar(new_cvar)));

                self.add_var(new_cvarnode, analyzer)?;
                analyzer.add_edge(new_cvarnode.0, *self, Edge::Context(ContextEdge::Variable));
                analyzer.add_edge(
                    new_cvarnode.0,
                    var.0,
                    Edge::Context(ContextEdge::InheritedVariable),
                );

                let fields = var.fielded_to_fields(analyzer)?;
                fields.iter().try_for_each(|field| {
                    Self::recursive_move_struct_field(new_cvarnode, *field, loc, analyzer)
                })?;
                Ok(new_cvarnode)
            } else {
                Ok(var)
            }
        } else {
            Ok(var)
        }
    }

    pub fn pop_n_latest_exprs(
        &self,
        n: usize,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Vec<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;

        let mut res = vec![];
        for _ in 0..n {
            if let Some(elem) = underlying_mut.expr_ret_stack.pop() {
                res.push(elem);
            } else {
                return Err(GraphError::StackLengthMismatch(format!(
                    "Expected {n} ExprRets on stack, but had fewer"
                )));
            }
        }

        res.into_iter()
            .map(|elem| self.maybe_move_expr(elem, loc, analyzer))
            .collect::<Result<Vec<_>, _>>()
    }

    /// Gets local vars that were assigned from a function return
    pub fn vars_assigned_from_fn_ret(&self, analyzer: &impl GraphBackend) -> Vec<ContextVarNode> {
        self.local_vars(analyzer)
            .iter()
            .flat_map(|(_name, var)| var.return_assignments(analyzer))
            .collect()
    }

    /// Gets local vars that were assigned from an external function return
    pub fn vars_assigned_from_ext_fn_ret(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Vec<ContextVarNode> {
        self.local_vars(analyzer)
            .iter()
            .flat_map(|(_name, var)| var.ext_return_assignments(analyzer))
            .collect()
    }
}
