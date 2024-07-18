//! Traits & blanket implementations that facilitate performing locally scoped function calls.

use crate::helper::CallerHelper;

use graph::{
    elem::Elem,
    nodes::{Builtin, Concrete, ContextNode, ExprRet, FunctionNode},
    AnalyzerBackend, GraphBackend, Node, VarType,
};
use shared::{ExprErr, GraphError, RangeArena};

use solang_parser::pt::Expression;

impl<T> InternalFuncCaller for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
}
/// A trait for performing internally scoped function calls (i.e. *NOT* `MyContract.func(...)`)
pub trait InternalFuncCaller:
    AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
    fn find_super_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
        maybe_named: Option<Vec<&str>>,
    ) -> Result<Option<FunctionNode>, GraphError> {
        if let Some(contract) = ctx.maybe_associated_contract(self)? {
            let supers = contract.super_contracts(self);
            let possible_funcs: Vec<_> = supers
                .iter()
                .filter_map(|con_node| {
                    con_node
                        .linearized_functions(self)
                        .ok()?
                        .into_iter()
                        .find(|(func_name, func_node)| {
                            if !func_name.starts_with(&name) {
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
                })
                .collect();
            self.find_func_inner(arena, ctx, name, num_inputs, possible_funcs, maybe_named)
        } else {
            Ok(None)
        }
    }

    fn find_func(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
        maybe_named: Option<Vec<&str>>,
    ) -> Result<Option<FunctionNode>, GraphError> {
        let funcs = ctx.visible_funcs(self)?;
        let possible_funcs = funcs
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
        self.find_func_inner(arena, ctx, name, num_inputs, possible_funcs, maybe_named)
    }

    fn find_func_inner(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        name: String,
        num_inputs: usize,
        possible_funcs: Vec<FunctionNode>,
        maybe_named: Option<Vec<&str>>,
    ) -> Result<Option<FunctionNode>, GraphError> {
        match possible_funcs.len() {
            0 => Ok(None),
            1 => Ok(Some(possible_funcs[0])),
            _ => {
                let stack = &ctx.underlying(self)?.expr_ret_stack;
                let len = stack.len();
                let mut inputs = stack[len.saturating_sub(num_inputs)..].to_vec();
                inputs.reverse();
                let resizeables: Vec<_> = inputs
                    .iter()
                    .map(|input| input.expect_single().ok())
                    .map(|idx| {
                        let Some(idx) = idx else {
                            return false;
                        };
                        match VarType::try_from_idx(self, idx) {
                            Some(VarType::BuiltIn(bn, _)) => {
                                matches!(
                                    self.node(bn),
                                    Node::Builtin(Builtin::Uint(_))
                                        | Node::Builtin(Builtin::Int(_))
                                        | Node::Builtin(Builtin::Bytes(_))
                                )
                            }
                            Some(VarType::Concrete(c)) => {
                                matches!(
                                    self.node(c),
                                    Node::Concrete(Concrete::Uint(_, _))
                                        | Node::Concrete(Concrete::Int(_, _))
                                        | Node::Concrete(Concrete::Bytes(_, _))
                                )
                            }
                            _ => false,
                        }
                    })
                    .collect();

                let inputs = ExprRet::Multi(inputs);
                Ok(self.disambiguate_fn_call(
                    arena,
                    &name,
                    resizeables,
                    &inputs,
                    &possible_funcs,
                    maybe_named,
                ))
            }
        }
    }
}
