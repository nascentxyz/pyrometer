//! Traits & blanket implementations that facilitate performing locally scoped function calls.

use crate::helper::CallerHelper;

use graph::{
    elem::Elem,
    nodes::{
        Builtin, Concrete, ContextNode, ContextVarNode, ContractNode, ExprRet, FunctionNode,
        StructNode,
    },
    AnalyzerBackend, GraphBackend, Node, TypeNode, VarType,
};
use shared::{ExprErr, GraphError, NodeIdx, RangeArena};

use solang_parser::pt::Expression;

use std::collections::BTreeMap;

impl<T> InternalFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
}
/// A trait for performing internally scoped function calls (i.e. *NOT* `MyContract.func(...)`)
pub trait InternalFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
    fn ordered_fn_inputs(&self, func: NodeIdx) -> Option<Vec<String>> {
        match self.node(func) {
            Node::ContextVar(..) => match ContextVarNode::from(func).ty(self).unwrap() {
                VarType::User(TypeNode::Func(func), _) => Some(func.ordered_param_names(self)),
                VarType::User(TypeNode::Struct(strukt), _) => {
                    Some(strukt.ordered_new_param_names(self))
                }
                VarType::User(TypeNode::Contract(con), _) => {
                    Some(con.ordered_new_param_names(self))
                }
                other => None,
            },
            Node::Function(..) => Some(FunctionNode::from(func).ordered_param_names(self)),
            Node::Struct(..) => Some(StructNode::from(func).ordered_new_param_names(self)),
            Node::Contract(..) => Some(ContractNode::from(func).ordered_new_param_names(self)),
            other => None,
        }
    }

    fn construct_func_input_strings(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        num_inputs: usize,
    ) -> Result<Vec<Vec<String>>, GraphError> {
        let stack = &ctx.underlying(self)?.expr_ret_stack;
        let len = stack.len();
        let mut inputs = stack[len.saturating_sub(num_inputs)..].to_vec();
        inputs.reverse();
        Ok(inputs
            .iter()
            .map(|input| input.expect_single().ok())
            .map(|idx| {
                let Some(idx) = idx else {
                    return vec![];
                };
                match VarType::try_from_idx(self, idx) {
                    Some(VarType::BuiltIn(bn, _)) => match self.node(bn) {
                        Node::Builtin(inner) => inner
                            .possible_upcast_builtins()
                            .into_iter()
                            .map(|b| b.basic_as_string())
                            .collect(),
                        _ => {
                            unreachable!()
                        }
                    },
                    Some(VarType::Concrete(cn)) => match self.node(cn) {
                        Node::Concrete(c) => c
                            .as_builtin()
                            .possible_upcast_builtins()
                            .into_iter()
                            .map(|b| b.basic_as_string())
                            .collect(),
                        _ => {
                            unreachable!()
                        }
                    },
                    Some(ty) => {
                        let Ok(ty_str) = ty.as_string(self) else {
                            return vec![];
                        };
                        vec![ty_str]
                    }
                    _ => vec![],
                }
            })
            .collect())
    }

    fn potential_funcs(
        &mut self,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        let funcs = ctx.visible_funcs(self)?;
        let mut possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).unwrap().starts_with(&format!("{name}(")))
            .filter(|func| {
                // filter by params
                func.params(self).len() == num_inputs
            })
            .filter(|func| {
                if let Some(ref named) = maybe_named {
                    func.params(self)
                        .iter()
                        .all(|param| named.contains(&&*param.name(self).unwrap()))
                } else {
                    true
                }
            })
            .copied()
            .collect::<Vec<_>>();
        possible_funcs.sort();
        possible_funcs.dedup();
        Ok(possible_funcs)
    }

    fn potential_super_funcs(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        if let Some(contract) = ctx.maybe_associated_contract(self)? {
            let mut possible_funcs: Vec<_> = contract
                .linearized_functions(self, true)?
                .into_iter()
                .filter(|(func_name, func_node)| {
                    if !func_name.starts_with(name) {
                        return false;
                    }

                    let params = func_node.params(self);

                    if params.len() != num_inputs {
                        return false;
                    }

                    if let Some(ref named) = maybe_named {
                        params
                            .iter()
                            .all(|param| named.contains(&&*param.name(self).unwrap()))
                    } else {
                        true
                    }
                })
                .map(|(_, node)| node)
                .collect();
            possible_funcs.sort();
            possible_funcs.dedup();
            Ok(possible_funcs)
        } else {
            Ok(vec![])
        }
    }

    fn find_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
        is_super: bool,
    ) -> Result<Option<(FunctionNode, BTreeMap<usize, usize>)>, GraphError> {
        let possible_funcs = if is_super {
            self.potential_super_funcs(arena, ctx, name, num_inputs, maybe_named)?
        } else {
            self.potential_funcs(ctx, name, num_inputs, maybe_named)?
        };

        println!(
            "potential funcs: {:?}",
            possible_funcs
                .iter()
                .map(|i| i.name(self).unwrap())
                .collect::<Vec<_>>()
        );

        let stack = &ctx.underlying(self)?.expr_ret_stack;
        let len = stack.len();
        let mut inputs = stack[len.saturating_sub(num_inputs)..].to_vec();
        inputs.reverse();

        let mut matched_funcs = possible_funcs
            .iter()
            .filter_map(|func| {
                let ordered_pos_to_input_pos: BTreeMap<_, _> =
                    if let Some(input_names) = &maybe_named {
                        let Some(ordered_names) = self.ordered_fn_inputs(func.0.into()) else {
                            return None;
                        };

                        if ordered_names[..] != input_names[..] {
                            ordered_names
                                .iter()
                                .enumerate()
                                .filter_map(|(i, n)| {
                                    Some((i, input_names.iter().position(|k| k == n)?))
                                })
                                .collect()
                        } else {
                            (0..input_names.len()).map(|i| (i, i)).collect()
                        }
                    } else {
                        (0..num_inputs).map(|i| (i, i)).collect()
                    };
                let tys = func
                    .params(self)
                    .iter()
                    .map(|param| VarType::try_from_idx(self, param.ty(self).unwrap()).unwrap())
                    .collect::<Vec<_>>();

                let all = tys.iter().enumerate().all(|(true_idx, ty)| {
                    let input_pos = ordered_pos_to_input_pos.get(&true_idx).unwrap();
                    inputs[*input_pos]
                        .implicitly_castable_to(self, ty)
                        .unwrap_or(false)
                });

                if all {
                    Some((*func, ordered_pos_to_input_pos))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if matched_funcs.len() == 1 {
            Ok(Some(matched_funcs.swap_remove(0)))
        } else {
            Ok(None)
        }
    }
}
