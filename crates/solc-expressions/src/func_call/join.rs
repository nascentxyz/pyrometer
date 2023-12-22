use crate::member_access::ListAccess;
use crate::{helper::CallerHelper, ExprErr, IntoExprErr};
use graph::elem::Elem;
use graph::elem::RangeElem;
use graph::nodes::ContextVar;
use graph::Range;
use graph::VarType;
use shared::StorageLocation;

use graph::{
    nodes::{ContextNode, ContextVarNode, ExprRet, FunctionNode, FunctionParamNode},
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, Node,
};

use solang_parser::pt::{Expression, Loc};

use std::collections::BTreeMap;

impl<T> FuncJoiner for T where
    T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized + GraphBackend + CallerHelper
{
}
/// A trait for calling a function
pub trait FuncJoiner:
    GraphBackend + AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized
{
    fn join(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        func: FunctionNode,
        params: &[FunctionParamNode],
        func_inputs: &[ContextVarNode],
    ) -> Result<bool, ExprErr> {
        // ensure no modifiers (for now)
        // if pure function:
        //      grab requirements for context
        //      grab return node's simplified range
        //      replace fundamentals with function inputs
        //      update ctx name in place

        if func.is_pure(self).into_expr_err(loc)? {
            // pure functions are guaranteed to not require the use of state, so
            // the only things we care about are function inputs and function outputs
            if let Some(body_ctx) = func.maybe_body_ctx(self) {
                // println!("replacement map: {replacement_map:#?}");
                if body_ctx
                    .underlying(self)
                    .into_expr_err(loc)?
                    .child
                    .is_some()
                {
                    let edges = body_ctx.successful_edges(self).into_expr_err(loc)?;
                    if edges.len() == 1 {
                        // let ret_nodes = edges[0].return_nodes(self)?;
                        // println!("return nodes: {:#?}", ret_nodes);
                    } else {
                        // println!("multiple edges: {}", edges.len());
                    }
                } else {
                    let inputs = body_ctx.input_variables(self);
                    let mut replacement_map = BTreeMap::default();
                    params
                        .iter()
                        .zip(func_inputs.iter())
                        .try_for_each(|(param, func_input)| {
                            if let Some(name) = param.maybe_name(self).into_expr_err(loc)? {
                                let mut new_cvar = func_input
                                    .latest_version(self)
                                    .underlying(self)
                                    .into_expr_err(loc)?
                                    .clone();
                                new_cvar.loc = Some(param.loc(self).unwrap());
                                // new_cvar.name = name.clone();
                                // new_cvar.display_name = name.clone();
                                new_cvar.is_tmp = false;
                                new_cvar.storage = if let Some(StorageLocation::Storage(_)) =
                                    param.underlying(self).unwrap().storage
                                {
                                    new_cvar.storage
                                } else {
                                    None
                                };

                                let replacement =
                                    ContextVarNode::from(self.add_node(Node::ContextVar(new_cvar)));

                                self.add_edge(
                                    replacement,
                                    *func_input,
                                    Edge::Context(ContextEdge::InputVariable),
                                );

                                if let Some(param_ty) =
                                    VarType::try_from_idx(self, param.ty(self).unwrap())
                                {
                                    if !replacement.ty_eq_ty(&param_ty, self).into_expr_err(loc)? {
                                        replacement
                                            .cast_from_ty(param_ty, self)
                                            .into_expr_err(loc)?;
                                    }
                                }

                                if let Some(_len_var) = replacement.array_to_len_var(self) {
                                    // bring the length variable along as well
                                    self.get_length(ctx, loc, *func_input, false).unwrap();
                                }

                                if let (Some(r), Some(r2)) =
                                    (replacement.range(self).unwrap(), param.range(self).unwrap())
                                {
                                    let new_min = r
                                        .range_min()
                                        .into_owned()
                                        .cast(r2.range_min().into_owned());
                                    let new_max = r
                                        .range_max()
                                        .into_owned()
                                        .cast(r2.range_max().into_owned());
                                    replacement
                                        .latest_version(self)
                                        .try_set_range_min(self, new_min)
                                        .into_expr_err(loc)?;
                                    replacement
                                        .latest_version(self)
                                        .try_set_range_max(self, new_max)
                                        .into_expr_err(loc)?;
                                    replacement
                                        .latest_version(self)
                                        .try_set_range_exclusions(self, r.exclusions)
                                        .into_expr_err(loc)?;
                                }

                                ctx.add_var(replacement, self).unwrap();
                                self.add_edge(
                                    replacement,
                                    ctx,
                                    Edge::Context(ContextEdge::Variable),
                                );

                                let Some(correct_input) = inputs
                                    .iter()
                                    .find(|input| input.name(self).unwrap() == name)
                                else {
                                    return Err(ExprErr::InvalidFunctionInput(
                                        loc,
                                        "Could not match input to parameter".to_string(),
                                    ));
                                };

                                let mut replacement_as_elem = Elem::from(replacement);
                                replacement_as_elem.arenaize(self).into_expr_err(loc)?;

                                if let Some(next) = correct_input.next_version(self) {
                                    replacement_map.insert(next.0, replacement_as_elem.clone());
                                }
                                replacement_map.insert(correct_input.0, replacement_as_elem);
                            }
                            Ok(())
                        })?;
                    // 1. Create a new variable with name `<func_name>.<return_number>`
                    // 2. Set the range to be the copy of the return's simplified range from the function
                    // 3. Replace the fundamentals with the input data
                    let mut rets: Vec<_> = body_ctx
                        .return_nodes(self)
                        .into_expr_err(loc)?
                        .iter()
                        .enumerate()
                        .map(|(i, (_, ret_node))| {
                            // println!("original return:");
                            // println!("  name: {}", ret_node.display_name(self).unwrap());
                            // println!("  range: {}", ret_node.simplified_range_string(self).unwrap().unwrap());
                            let mut new_var = ret_node.underlying(self).unwrap().clone();
                            let new_name = format!("{}.{i}", func.name(self).unwrap());
                            new_var.name = new_name.clone();
                            new_var.display_name = new_name;
                            if let Some(mut range) = new_var.ty.take_range() {
                                replacement_map.iter().for_each(|(replace, replacement)| {
                                    range.replace_dep((*replace).into(), replacement.clone(), self);
                                });

                                range.cache_eval(self).unwrap();

                                new_var.ty.set_range(range).unwrap();
                            }

                            let new_cvar =
                                ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));
                            self.add_edge(new_cvar, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.add_var(new_cvar, self).unwrap();
                            // let new_range =  new_cvar.range(self).unwrap().unwrap();

                            // println!("new return:");
                            // println!("  name: {}", new_cvar.display_name(self).unwrap());
                            // println!("  range: {}", new_cvar.range_string(self).unwrap().unwrap());
                            ExprRet::Single(new_cvar.into())
                        })
                        .collect();

                    // println!("requires:");
                    body_ctx
                        .ctx_deps(self)
                        .into_expr_err(loc)?
                        .iter()
                        .for_each(|dep| {
                            // println!("  name: {}", dep.display_name(self).unwrap());
                            let mut new_var = dep.underlying(self).unwrap().clone();
                            if let Some(mut range) = new_var.ty.take_range() {
                                replacement_map.iter().for_each(|(replace, replacement)| {
                                    range.replace_dep((*replace).into(), replacement.clone(), self);
                                });

                                range.cache_eval(self).unwrap();
                                new_var.ty.set_range(range).unwrap();
                            }

                            let new_cvar =
                                ContextVarNode::from(self.add_node(Node::ContextVar(new_var)));
                            self.add_edge(new_cvar, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.add_var(new_cvar, self).unwrap();
                            ctx.add_ctx_dep(new_cvar, self).unwrap();
                        });

                    func.returns(self)
                        .collect::<Vec<_>>()
                        .into_iter()
                        .for_each(|ret| {
                            if let Some(var) = ContextVar::maybe_new_from_func_ret(
                                self,
                                ret.underlying(self).unwrap().clone(),
                            ) {
                                let cvar = self.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), self).unwrap();
                                self.add_edge(cvar, ctx, Edge::Context(ContextEdge::Variable));
                                rets.push(ExprRet::Single(cvar));
                            }
                        });

                    ctx.underlying_mut(self).into_expr_err(loc)?.path = format!(
                        "{}.{}.resume{{ {} }}",
                        ctx.path(self),
                        func.name(self).unwrap(),
                        ctx.associated_fn_name(self).unwrap()
                    );
                    ctx.push_expr(ExprRet::Multi(rets), self)
                        .into_expr_err(loc)?;
                    return Ok(true);
                }
            }

            // update path name to reflect that we called the function
        }

        Ok(false)
        // todo!("Joining not supported yet");
    }
}
