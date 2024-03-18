use crate::Analyzer;

use graph::{
    nodes::{
        BlockNode, Builtin, Concrete, ConcreteNode, Function, FunctionNode, FunctionParam,
        FunctionParamNode, FunctionReturn, MsgNode,
    },
    AnalyzerBackend, Edge, Node, VarType,
};
use shared::{AnalyzerLike, GraphLike, JoinStats, NodeIdx};
use solc_expressions::{ExprErr, IntoExprErr};

use ahash::AHashMap;
use ethers_core::types::U256;
use solang_parser::{helpers::CodeLocation, pt::Expression};

use std::collections::BTreeMap;

impl AnalyzerBackend for Analyzer {}

impl AnalyzerLike for Analyzer {
    type Expr = Expression;
    type ExprErr = ExprErr;
    type MsgNode = MsgNode;
    type BlockNode = BlockNode;

    type Function = Function;
    type FunctionNode = FunctionNode;
    type FunctionParam = FunctionParam;
    type FunctionReturn = FunctionReturn;
    type Builtin = Builtin;

    fn builtin_fn_nodes(&self) -> &AHashMap<String, NodeIdx> {
        &self.builtin_fn_nodes
    }

    fn builtin_fn_nodes_mut(&mut self) -> &mut AHashMap<String, NodeIdx> {
        &mut self.builtin_fn_nodes
    }

    fn max_depth(&self) -> usize {
        self.max_depth
    }

    fn max_width(&self) -> usize {
        self.max_width
    }

    fn add_expr_err(&mut self, err: ExprErr) {
        if self.debug_panic() {
            panic!("Encountered an error: {err:?}");
        }
        if !self.expr_errs.contains(&err) {
            self.expr_errs.push(err);
        }
    }

    fn expr_errs(&self) -> Vec<ExprErr> {
        self.expr_errs.clone()
    }

    fn entry(&self) -> NodeIdx {
        self.entry
    }

    fn parse_fn(&self) -> FunctionNode {
        self.parse_fn
    }

    fn msg(&mut self) -> MsgNode {
        self.msg
    }

    fn block(&mut self) -> BlockNode {
        self.block
    }

    fn builtin_fns(&self) -> &AHashMap<String, Function> {
        &self.builtin_fns
    }

    fn builtin_fn_inputs(&self) -> &AHashMap<String, (Vec<FunctionParam>, Vec<FunctionReturn>)> {
        &self.builtin_fn_inputs
    }

    fn builtins(&self) -> &AHashMap<Builtin, NodeIdx> {
        &self.builtins
    }
    fn builtins_mut(&mut self) -> &mut AHashMap<Builtin, NodeIdx> {
        &mut self.builtins
    }
    fn user_types(&self) -> &AHashMap<String, NodeIdx> {
        &self.user_types
    }
    fn user_types_mut(&mut self) -> &mut AHashMap<String, NodeIdx> {
        &mut self.user_types
    }

    fn parse_expr(&mut self, expr: &Expression, parent: Option<NodeIdx>) -> NodeIdx {
        use Expression::*;
        match expr {
            Type(_loc, ty) => {
                if let Some(builtin) = Builtin::try_from_ty(ty.clone(), self) {
                    if let Some(idx) = self.builtins.get(&builtin) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(builtin.clone()));
                        self.builtins.insert(builtin, idx);
                        idx
                    }
                } else if let Some(idx) = self.complicated_parse(expr, parent) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
                } else {
                    0.into()
                }
            }
            Variable(ident) => {
                if let Some(idx) = self.user_types.get(&ident.name) {
                    *idx
                } else {
                    let node = self.add_node(Node::Unresolved(ident.clone()));
                    self.user_types.insert(ident.name.clone(), node);
                    node
                }
            }
            ArraySubscript(_loc, ty_expr, None) => {
                let inner_ty = self.parse_expr(ty_expr, parent);
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let dyn_b = Builtin::Array(var_type);
                    if let Some(idx) = self.builtins.get(&dyn_b) {
                        *idx
                    } else {
                        let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                        self.builtins.insert(dyn_b, idx);
                        idx
                    }
                } else {
                    inner_ty
                }
            }
            ArraySubscript(loc, ty_expr, Some(idx_expr)) => {
                let inner_ty = self.parse_expr(ty_expr, parent);
                let idx = self.parse_expr(idx_expr, parent);
                if let Some(var_type) = VarType::try_from_idx(self, inner_ty) {
                    let res = ConcreteNode::from(idx)
                        .underlying(self)
                        .into_expr_err(*loc)
                        .cloned();
                    if let Some(concrete) = self.add_if_err(res) {
                        if let Some(size) = concrete.uint_val() {
                            let dyn_b = Builtin::SizedArray(size, var_type);
                            if let Some(idx) = self.builtins.get(&dyn_b) {
                                *idx
                            } else {
                                let idx = self.add_node(Node::Builtin(dyn_b.clone()));
                                self.builtins.insert(dyn_b, idx);
                                idx
                            }
                        } else {
                            inner_ty
                        }
                    } else {
                        inner_ty
                    }
                } else {
                    inner_ty
                }
            }
            NumberLiteral(_loc, integer, exponent, _unit) => {
                let int = U256::from_dec_str(integer).unwrap();
                let val = if !exponent.is_empty() {
                    let exp = U256::from_dec_str(exponent).unwrap();
                    int * U256::from(10).pow(exp)
                } else {
                    int
                };

                self.add_node(Node::Concrete(Concrete::Uint(256, val)))
            }
            _ => {
                if let Some(idx) = self.complicated_parse(expr, parent) {
                    self.add_if_err(idx.expect_single().into_expr_err(expr.loc()))
                        .unwrap_or(0.into())
                } else {
                    0.into()
                }
            }
        }
    }

    fn builtin_or_add(&mut self, builtin: Builtin) -> NodeIdx {
        if let Some(idx) = self.builtins().get(&builtin) {
            *idx
        } else {
            let idx = self.add_node(Node::Builtin(builtin.clone()));
            self.builtins_mut().insert(builtin, idx);
            idx
        }
    }

    fn builtin_fn_or_maybe_add(&mut self, builtin_name: &str) -> Option<NodeIdx>
    where
        Self: std::marker::Sized,
    {
        if let Some(idx) = self.builtin_fn_nodes().get(builtin_name) {
            Some(*idx)
        } else if let Some(func) = self.builtin_fns().get(builtin_name) {
            let (inputs, outputs) = self
                .builtin_fn_inputs()
                .get(builtin_name)
                .expect("builtin func but no inputs")
                .clone();
            let func_node = self.add_node(Node::Function(func.clone()));
            let mut params_strs = vec![];
            inputs.into_iter().for_each(|input| {
                let input_node = self.add_node(input);
                params_strs.push(FunctionParamNode::from(input_node).ty_str(self).unwrap());
                self.add_edge(input_node, func_node, Edge::FunctionParam);
            });
            outputs.into_iter().for_each(|output| {
                let output_node = self.add_node(output);
                self.add_edge(output_node, func_node, Edge::FunctionReturn);
            });

            self.add_edge(func_node, self.entry(), Edge::Func);

            self.builtin_fn_nodes_mut()
                .insert(builtin_name.to_string(), func_node);
            Some(func_node)
        } else {
            None
        }
    }

    fn debug_panic(&self) -> bool {
        self.debug_panic
    }

    fn fn_calls_fns(&self) -> &BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>> {
        &self.fn_calls_fns
    }
    fn fn_calls_fns_mut(&mut self) -> &mut BTreeMap<Self::FunctionNode, Vec<Self::FunctionNode>> {
        &mut self.fn_calls_fns
    }

    fn join_stats_mut(&mut self) -> &mut JoinStats {
        &mut self.join_stats
    }
}
