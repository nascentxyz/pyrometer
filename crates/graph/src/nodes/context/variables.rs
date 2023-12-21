use crate::{
    nodes::{ContextNode, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, GraphError, Node,
};

use solang_parser::pt::Loc;

use std::collections::BTreeMap;

impl ContextNode {
    /// Debug print the stack
    pub fn debug_expr_stack(&self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        let underlying_mut = self.underlying(analyzer)?;
        underlying_mut
            .expr_ret_stack
            .iter()
            .for_each(|elem| println!("{}", elem.debug_str(analyzer)));
        Ok(())
    }

    /// Add a variable to this context
    pub fn add_var(
        &self,
        var: ContextVarNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        // var.cache_range(analyzer)?;
        let name = var.name(analyzer)?;
        let vars = &mut self.underlying_mut(analyzer)?.cache.vars;
        vars.insert(name, var);
        Ok(())
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

    /// Gets all variables associated with a context
    pub fn vars<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> &'a BTreeMap<String, ContextVarNode> {
        &self.underlying(analyzer).unwrap().cache.vars
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
    pub fn new_tmp(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<usize, GraphError> {
        let context = self.underlying_mut(analyzer)?;
        let ret = context.tmp_var_ctr;
        context.tmp_var_ctr += 1;
        Ok(ret)
    }

    /// Push an expression return into the temporary stack
    pub fn push_tmp_expr(
        &self,
        expr_ret: ExprRet,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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

    /// May move the variable from an old context to this context
    pub fn maybe_move_var(
        &self,
        var: ContextVarNode,
        loc: Loc,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<ContextVarNode, GraphError> {
        let var = var.latest_version(analyzer);
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

    /// Pop the latest expression return off the stack
    #[tracing::instrument(level = "trace", skip_all)]
    pub fn pop_expr_latest(
        &self,
        loc: Loc,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
