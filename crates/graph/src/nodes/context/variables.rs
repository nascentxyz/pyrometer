use crate::{
    nodes::{ContextNode, ContextVarNode, ExprRet, VarNode},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node, TypeNode,
};
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
    pub fn debug_expr_stack(&self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        let underlying_mut = self.underlying(analyzer)?;
        underlying_mut
            .expr_ret_stack
            .iter()
            .enumerate()
            .for_each(|(i, elem)| println!("{i}. {}", elem.debug_str(analyzer)));
        Ok(())
    }

    /// Debug print the temprorary stack
    pub fn debug_tmp_expr_stack(&self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        let underlying_mut = self.underlying(analyzer)?;
        underlying_mut
            .tmp_expr
            .iter()
            .enumerate()
            .filter(|(_i, maybe_elem)| maybe_elem.is_some())
            .for_each(|(i, elem)| println!("{i}. {}", elem.clone().unwrap().debug_str(analyzer)));
        Ok(())
    }

    /// Add a variable to this context
    pub fn add_var(
        &self,
        var: ContextVarNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        // var.cache_range(analyzer)?;
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

    /// Gets a variable by name or recurses up the relevant scopes/contexts until it is found
    pub fn var_by_name_or_recurse(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        if let Some(var) = self.var_by_name(analyzer, name) {
            Ok(Some(var))
        } else if let Some(parent) = self.ancestor_in_fn(analyzer, self.associated_fn(analyzer)?)? {
            parent.var_by_name_or_recurse(analyzer, name)
        } else if let Some(parent) = self.underlying(analyzer)?.continuation_of {
            parent.var_by_name_or_recurse(analyzer, name)
        } else {
            Ok(None)
        }
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
        let fields = member.struct_to_fields(analyzer)?;
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
            .vars
            .clone()
            .into_iter()
            .filter(|(_, var)| var.is_storage(analyzer).unwrap())
            .map(|(_, var)| var)
            .collect::<Vec<_>>()
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
        println!("getting storage vars for: {}", self.path(analyzer));
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

    /// Push an expression return into the temporary stack
    pub fn push_tmp_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        underlying_mut.tmp_expr.push(Some(expr_ret));
        Ok(())
    }

    /// Append a new expression return to an expression return
    /// currently in the temporary stack
    pub fn append_tmp_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut impl AnalyzerBackend,
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

    /// Pops a from the temporary ExprRet stack
    pub fn pop_tmp_expr(
        &self,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Option<ExprRet>, GraphError> {
        let underlying_mut = self.underlying_mut(analyzer)?;
        if let Some(Some(expr)) = underlying_mut.tmp_expr.pop() {
            Ok(Some(self.maybe_move_expr(expr, loc, analyzer)?))
        } else {
            Ok(None)
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
        &self,
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

        let sub_fields = field.struct_to_fields(analyzer)?;
        sub_fields.iter().try_for_each(|sub_field| {
            self.recursive_move_struct_field(new_cvarnode, *sub_field, loc, analyzer)
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

                let fields = var.struct_to_fields(analyzer)?;
                fields.iter().try_for_each(|field| {
                    self.recursive_move_struct_field(new_cvarnode, *field, loc, analyzer)
                })?;
                Ok(new_cvarnode)
            } else {
                Ok(var)
            }
        } else {
            Ok(var)
        }
    }

    /// Pop the latest expression return off the stack
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn pop_expr_latest(
        &self,
        loc: Loc,
        analyzer: &mut impl AnalyzerBackend,
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
