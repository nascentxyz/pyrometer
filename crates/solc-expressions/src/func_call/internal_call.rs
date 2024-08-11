//! Traits & blanket implementations that facilitate performing locally scoped function calls.

use crate::{
    helper::CallerHelper,
    member_access::{BuiltinAccess, LibraryAccess},
};

use graph::{
    nodes::{
        BuiltInNode, ContextNode, ContextVarNode, ContractNode, ExprRet, FunctionNode, StructNode,
    },
    AnalyzerBackend, GraphBackend, Node, TypeNode, VarType,
};
use shared::{ExprErr, GraphError, NodeIdx};

use solang_parser::pt::{Expression, FunctionTy};

use std::collections::BTreeMap;

pub struct FindFunc {
    pub func: FunctionNode,
    pub reordering: BTreeMap<usize, usize>,
    pub was_lib_func: bool,
}

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
                _ => None,
            },
            Node::Function(..) => Some(FunctionNode::from(func).ordered_param_names(self)),
            Node::Struct(..) => Some(StructNode::from(func).ordered_new_param_names(self)),
            Node::Contract(..) => Some(ContractNode::from(func).ordered_new_param_names(self)),
            _ => None,
        }
    }

    fn potential_lib_funcs(
        &mut self,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
        maybe_member: Option<NodeIdx>,
    ) -> Result<Vec<(FunctionNode, bool)>, GraphError> {
        let Some(member) = maybe_member else {
            return Ok(vec![]);
        };

        let (var_ty, is_storage) = match self.node(member) {
            Node::ContextVar(..) => {
                let var = ContextVarNode::from(member);
                (var.ty(self).unwrap().clone(), var.is_storage(self)?)
            }
            _ => (VarType::try_from_idx(self, member).unwrap(), false),
        };

        let mut funcs = self.possible_library_funcs(ctx, var_ty.ty_idx());
        match var_ty {
            VarType::BuiltIn(_, _) => {
                if let Some((ret, is_lib)) = self.builtin_builtin_fn(
                    BuiltInNode::from(var_ty.ty_idx()),
                    name,
                    num_inputs,
                    is_storage,
                )? {
                    if is_lib {
                        funcs.push(ret);
                    }
                }
            }
            VarType::User(TypeNode::Ty(ty), _) => {
                if let Some(func) = self.specialize_ty_fn(ty, name)? {
                    funcs.push(func)
                }
            }
            _ => {}
        }

        let mut possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).unwrap().starts_with(&format!("{name}(")))
            .map(|func| (func, func.params(self)))
            .filter(|(_, params)| {
                // filter by param length, add 1 to inputs due to passing the member
                params.len() == (num_inputs + 1)
            })
            .filter(|(_, params)| {
                if let Some(ref named) = maybe_named {
                    // we skip the first because its not named when used a library function
                    params
                        .iter()
                        .skip(1)
                        .all(|param| named.contains(&&*param.name(self).unwrap()))
                } else {
                    true
                }
            })
            .map(|(func, _)| (*func, true))
            .collect::<Vec<_>>();
        possible_funcs.sort();
        possible_funcs.dedup();
        Ok(possible_funcs)
    }

    fn potential_member_funcs(
        &mut self,
        name: &str,
        member: NodeIdx,
        num_inputs: usize,
    ) -> Result<(Vec<FunctionNode>, bool), GraphError> {
        match self.node(member) {
            // Only instantiated & abstract contracts and bytes & strings have non-library functions
            Node::ContextVar(..) => {
                let var = ContextVarNode::from(member);
                match var.ty(self)? {
                    VarType::User(TypeNode::Contract(con_node), _) => {
                        let c = *con_node;
                        let func_mapping = c.linearized_functions(self, false)?;
                        Ok((func_mapping.values().copied().collect(), false))
                    }
                    _ => Ok((vec![], false)),
                }
            }
            Node::Contract(..) => {
                let c = ContractNode::from(member);
                let func_mapping = c.linearized_functions(self, false)?;
                Ok((func_mapping.values().copied().collect(), false))
            }
            Node::Builtin(_) => {
                if let Some((ret, lib)) =
                    self.builtin_builtin_fn(BuiltInNode::from(member), name, num_inputs, false)?
                {
                    if !lib {
                        return Ok((vec![ret], true));
                    }
                }
                Ok((vec![], false))
            }
            _ => Ok((vec![], false)),
        }
    }

    fn potential_funcs(
        &mut self,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
        maybe_member: Option<NodeIdx>,
    ) -> Result<(Vec<(FunctionNode, bool)>, bool), GraphError> {
        let funcs = if let Some(member) = maybe_member {
            let (mut funcs, early_end) = self.potential_member_funcs(name, member, num_inputs)?;
            if early_end && funcs.len() == 1 {
                return Ok((vec![(funcs.swap_remove(0), false)], true));
            } else {
                funcs
            }
        } else {
            ctx.visible_funcs(self)?
        };

        let mut possible_funcs = funcs
            .iter()
            .filter(|func| func.name(self).unwrap().starts_with(&format!("{name}(")))
            .map(|func| (func, func.params(self)))
            .filter(|(_, params)| {
                // filter by params
                params.len() == num_inputs
            })
            .filter(|(_, params)| {
                if let Some(ref named) = maybe_named {
                    params
                        .iter()
                        .all(|param| named.contains(&&*param.name(self).unwrap()))
                } else {
                    true
                }
            })
            .map(|(func, _)| (*func, false))
            .collect::<Vec<_>>();
        possible_funcs.extend(self.potential_lib_funcs(
            ctx,
            name,
            num_inputs,
            maybe_named,
            maybe_member,
        )?);
        possible_funcs.sort();
        possible_funcs.dedup();
        Ok((possible_funcs, false))
    }

    fn potential_super_funcs(
        &mut self,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
    ) -> Result<Vec<(FunctionNode, bool)>, GraphError> {
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
            Ok(possible_funcs.into_iter().map(|f| (f, false)).collect())
        } else {
            Ok(vec![])
        }
    }

    fn find_modifier(
        &mut self,
        ctx: ContextNode,
        name: &str,
        constructor: bool,
    ) -> Result<Vec<FunctionNode>, GraphError> {
        let mut potential_mods = if constructor {
            let contract = ctx.associated_contract(self)?;
            let inherited = contract.all_inherited_contracts(self);
            let cons = inherited
                .iter()
                .filter_map(|c| c.constructor(self))
                .collect::<Vec<_>>();
            cons.into_iter()
                .filter(|func| {
                    let res = matches!(func.ty(self), Ok(FunctionTy::Constructor));
                    let contract = func.maybe_associated_contract(self).unwrap();
                    res && contract.name(self).unwrap().starts_with(&name.to_string())
                })
                .collect::<Vec<_>>()
        } else {
            let mods = ctx.visible_modifiers(self)?;
            mods.into_iter()
                .filter(|func| matches!(func.ty(self), Ok(FunctionTy::Modifier)))
                .filter(|func| func.name(self).unwrap().starts_with(&format!("{name}(")))
                .collect::<Vec<_>>()
        };

        potential_mods.sort();
        potential_mods.dedup();
        if potential_mods.len() == 1 {
            Ok(vec![potential_mods.swap_remove(0)])
        } else {
            Ok(potential_mods)
        }
    }

    fn find_func(
        &mut self,
        ctx: ContextNode,
        name: &str,
        num_inputs: usize,
        maybe_named: &Option<Vec<&str>>,
        is_super: bool,
        member_access: Option<NodeIdx>,
    ) -> Result<Vec<FindFunc>, GraphError> {
        let possible_funcs = if is_super {
            self.potential_super_funcs(ctx, name, num_inputs, maybe_named)?
        } else {
            let (mut funcs, early_end) =
                self.potential_funcs(ctx, name, num_inputs, maybe_named, member_access)?;
            if early_end {
                return Ok(vec![FindFunc {
                    func: funcs.swap_remove(0).0,
                    reordering: (0..num_inputs).map(|i| (i, i)).collect(),
                    was_lib_func: false,
                }]);
            } else {
                funcs
            }
        };

        let stack = &ctx.underlying(self)?.expr_ret_stack;
        let len = stack.len();
        let mut inputs = stack[len.saturating_sub(num_inputs)..].to_vec();
        inputs.reverse();

        let matched_funcs = possible_funcs
            .iter()
            .filter_map(|(func, lib_func)| {
                let ordered_pos_to_input_pos: BTreeMap<_, _> =
                    if let Some(input_names) = &maybe_named {
                        let mut ordered_names = self.ordered_fn_inputs(func.0.into())?;
                        ordered_names = if *lib_func {
                            // remove the first input for a lib function
                            ordered_names.remove(0);
                            ordered_names
                        } else {
                            ordered_names
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

                let checked_params = if *lib_func {
                    // remove the first element because its already typechecked in a lib func
                    let mut params = func.params(self);
                    params.remove(0);
                    params
                } else {
                    func.params(self)
                };

                let tys = checked_params
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
                    Some(FindFunc {
                        func: *func,
                        reordering: ordered_pos_to_input_pos,
                        was_lib_func: *lib_func,
                    })
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        Ok(matched_funcs)
    }
}
