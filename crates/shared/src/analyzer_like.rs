use crate::{GraphLike, NodeIdx, RangeArena};

use ahash::AHashMap;

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, Default)]
pub struct JoinStats {
    pub pure_no_children_joins: JoinStat,
    pub pure_children_no_forks_joins: JoinStat,
    pub pure_children_forks_joins: JoinStat,

    pub view_no_children_joins: JoinStat,
    pub view_children_no_forks_joins: JoinStat,
    pub view_children_forks_joins: JoinStat,

    pub mut_no_children_joins: JoinStat,
    pub mut_children_no_forks_joins: JoinStat,
    pub mut_children_forks_joins: JoinStat,
}

impl JoinStats {
    pub fn total_joins(&self) -> usize {
        self.total_pure_joins() + self.total_view_joins() + self.total_mut_joins()
    }

    pub fn completed_joins(&self) -> usize {
        self.completed_pure_joins() + self.completed_view_joins() + self.completed_mut_joins()
    }

    pub fn reduced_vars(&self) -> usize {
        self.pure_reduced_vars() + self.view_reduced_vars() + self.mut_reduced_vars()
    }

    pub fn total_pure_joins(&self) -> usize {
        self.pure_no_children_joins.num_joins
            + self.pure_children_no_forks_joins.num_joins
            + self.pure_children_forks_joins.num_joins
    }

    pub fn completed_pure_joins(&self) -> usize {
        self.pure_no_children_joins.completed_joins
            + self.pure_children_no_forks_joins.completed_joins
            + self.pure_children_forks_joins.completed_joins
    }

    pub fn pure_reduced_vars(&self) -> usize {
        self.pure_no_children_joins.vars_reduced
            + self.pure_children_no_forks_joins.vars_reduced
            + self.pure_children_forks_joins.vars_reduced
    }

    pub fn total_view_joins(&self) -> usize {
        self.view_no_children_joins.num_joins
            + self.view_children_no_forks_joins.num_joins
            + self.view_children_forks_joins.num_joins
    }

    pub fn completed_view_joins(&self) -> usize {
        self.view_no_children_joins.completed_joins
            + self.view_children_no_forks_joins.completed_joins
            + self.view_children_forks_joins.completed_joins
    }

    pub fn view_reduced_vars(&self) -> usize {
        self.view_no_children_joins.vars_reduced
            + self.view_children_no_forks_joins.vars_reduced
            + self.view_children_forks_joins.vars_reduced
    }

    pub fn total_mut_joins(&self) -> usize {
        self.mut_no_children_joins.num_joins
            + self.mut_children_no_forks_joins.num_joins
            + self.mut_children_forks_joins.num_joins
    }

    pub fn completed_mut_joins(&self) -> usize {
        self.mut_no_children_joins.completed_joins
            + self.mut_children_no_forks_joins.completed_joins
            + self.mut_children_forks_joins.completed_joins
    }

    pub fn mut_reduced_vars(&self) -> usize {
        self.mut_no_children_joins.vars_reduced
            + self.mut_children_no_forks_joins.vars_reduced
            + self.mut_children_forks_joins.vars_reduced
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct JoinStat {
    pub num_joins: usize,
    pub completed_joins: usize,
    pub vars_reduced: usize,
}

pub trait AnalyzerLike: GraphLike {
    /// The expression type
    type Expr;
    /// An error when parsing an expression
    type ExprErr;

    /// Type of the `msg` node
    type MsgNode;
    /// Type of the `block` node
    type BlockNode;

    /// Type of a function
    type Function;
    /// Node of a function type
    type FunctionNode;
    /// Type of a function input parameter
    type FunctionParam;
    /// Type of a function return paramter
    type FunctionReturn;

    /// Type of a builtin
    type Builtin;

    /// Gets the builtin functions map
    fn builtin_fns(&self) -> &AHashMap<String, Self::Function>;
    /// Mutably gets the builtin functions map
    fn builtin_fn_nodes_mut(&mut self) -> &mut AHashMap<String, NodeIdx>;
    /// Gets the builtin function nodes mapping
    fn builtin_fn_nodes(&self) -> &AHashMap<String, NodeIdx>;
    /// Returns the configured max call depth
    fn max_depth(&self) -> usize;
    /// Returns the configured max fork width
    fn max_width(&self) -> usize;
    fn user_types(&self) -> &AHashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut AHashMap<String, NodeIdx>;
    fn parse_expr(
        &mut self,
        arena: &mut RangeArena<Self::RangeElem>,
        expr: &Self::Expr,
        parent: Option<NodeIdx>,
    ) -> NodeIdx;
    fn msg(&mut self) -> Self::MsgNode;
    fn block(&mut self) -> Self::BlockNode;
    fn entry(&self) -> NodeIdx;
    fn parse_fn(&self) -> Self::FunctionNode;
    fn add_expr_err(&mut self, err: Self::ExprErr);
    fn expr_errs(&self) -> Vec<Self::ExprErr>;

    fn builtin_fn_inputs(
        &self,
    ) -> &AHashMap<String, (Vec<Self::FunctionParam>, Vec<Self::FunctionReturn>)>;
    fn builtins(&self) -> &AHashMap<Self::Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut AHashMap<Self::Builtin, NodeIdx>;
    fn builtin_or_add(&mut self, builtin: Self::Builtin) -> NodeIdx;
    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized;

    fn debug_panic(&self) -> bool;

    fn fn_calls_fns(&self) -> &BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn fn_calls_fns_mut(&mut self) -> &mut BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn add_fn_call(&mut self, caller: Self::FunctionNode, callee: Self::FunctionNode)
    where
        Self::FunctionNode: Ord,
    {
        let calls = self.fn_calls_fns_mut();
        let entry = calls.entry(caller).or_default();
        if !entry.contains(&callee) {
            entry.push(callee)
        }
    }

    fn add_if_err<T>(&mut self, err: Result<T, Self::ExprErr>) -> Option<T>
    where
        Self::ExprErr: std::fmt::Debug,
    {
        match err {
            Ok(t) => Some(t),
            Err(e) => {
                self.add_expr_err(e);
                None
            }
        }
    }

    fn join_stats_mut(&mut self) -> &mut JoinStats;
    fn handled_funcs(&self) -> &[Self::FunctionNode];
    fn handled_funcs_mut(&mut self) -> &mut Vec<Self::FunctionNode>;
}
