use std::collections::BTreeMap;
use crate::{GraphLike, NodeIdx};
use std::collections::HashMap;

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
    fn builtin_fns(&self) -> &HashMap<String, Self::Function>;
    /// Mutably gets the builtin functions map
    fn builtin_fn_nodes_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    /// Gets the builtin function nodes mapping
    fn builtin_fn_nodes(&self) -> &HashMap<String, NodeIdx>;
    /// Returns the configured max call depth
    fn max_depth(&self) -> usize;
    /// Returns the configured max fork width
    fn max_width(&self) -> usize;
    fn user_types(&self) -> &HashMap<String, NodeIdx>;
    fn user_types_mut(&mut self) -> &mut HashMap<String, NodeIdx>;
    fn parse_expr(&mut self, expr: &Self::Expr, parent: Option<NodeIdx>) -> NodeIdx;
    fn msg(&mut self) -> Self::MsgNode;
    fn block(&mut self) -> Self::BlockNode;
    fn entry(&self) -> NodeIdx;
    fn parse_fn(&self) -> Self::FunctionNode;
    fn add_expr_err(&mut self, err: Self::ExprErr);
    fn expr_errs(&self) -> Vec<Self::ExprErr>;

    fn builtin_fn_inputs(
        &self,
    ) -> &HashMap<String, (Vec<Self::FunctionParam>, Vec<Self::FunctionReturn>)>;
    fn builtins(&self) -> &HashMap<Self::Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut HashMap<Self::Builtin, NodeIdx>;
    fn builtin_or_add(&mut self, builtin: Self::Builtin) -> NodeIdx;
    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized;

    fn debug_panic(&self) -> bool;

    fn fn_calls_fns(&self) -> &BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn fn_calls_fns_mut(&mut self) -> &mut BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>>;
    fn add_fn_call(&mut self, caller: Self::FunctionNode, callee: Self::FunctionNode)
        where Self::FunctionNode: Ord
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
}
