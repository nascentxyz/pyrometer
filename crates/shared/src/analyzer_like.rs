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
    fn add_expr_err(&mut self, err: Self::ExprErr);
    fn expr_errs(&self) -> Vec<Self::ExprErr>;

    fn builtin_fn_inputs(&self) -> &HashMap<String, (Vec<Self::FunctionParam>, Vec<Self::FunctionReturn>)>;
    fn builtins(&self) -> &HashMap<Self::Builtin, NodeIdx>;
    fn builtins_mut(&mut self) -> &mut HashMap<Self::Builtin, NodeIdx>;
    
    fn builtin_or_add(&mut self, builtin: Self::Builtin) -> NodeIdx;
    //  {
    //     if let Some(idx) = self.builtins().get(&builtin) {
    //         *idx
    //     } else {
    //         let idx = self.add_node(Node::Builtin(builtin.clone()));
    //         self.builtins_mut().insert(builtin, idx);
    //         idx
    //     }
    // }
    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized;
    // {
    //     if let Some(idx) = self.builtin_fn_nodes().get(builtin_name) {
    //         Some(*idx)
    //     } else if let Some(func) = self.builtin_fns().get(builtin_name) {
    //         let (inputs, outputs) = self
    //             .builtin_fn_inputs()
    //             .get(builtin_name)
    //             .expect("builtin func but no inputs")
    //             .clone();
    //         let func_node = self.add_node(Node::Function(func.clone()));
    //         let mut params_strs = vec![];
    //         inputs.into_iter().for_each(|input| {
    //             let input_node = self.add_node(input);
    //             params_strs.push(FunctionParamNode::from(input_node).ty_str(self).unwrap());
    //             self.add_edge(input_node, func_node, Edge::FunctionParam);
    //         });
    //         outputs.into_iter().for_each(|output| {
    //             let output_node = self.add_node(output);
    //             self.add_edge(output_node, func_node, Edge::FunctionReturn);
    //         });

    //         self.add_edge(func_node, self.entry(), Edge::Func);

    //         self.builtin_fn_nodes_mut()
    //             .insert(builtin_name.to_string(), func_node);
    //         Some(func_node)
    //     } else {
    //         None
    //     }
    // }


    fn add_if_err<T>(&mut self, err: Result<T, Self::ExprErr>) -> Option<T> {
        match err {
            Ok(t) => Some(t),
            Err(e) => {
                self.add_expr_err(e);
                None
            }
        }
    }
}