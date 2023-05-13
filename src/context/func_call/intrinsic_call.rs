use crate::context::{
    exprs::{Array, MemberAccess, Require},
    ContextBuilder,
};
use crate::context::{ExprErr, IntoExprErr};
use ethers_core::types::U256;

use shared::analyzer::Search;
use shared::analyzer::{AnalyzerLike, GraphLike};
use shared::nodes::Concrete;

use shared::{
    context::*,
    nodes::{Builtin, VarType},
    range::{elem_ty::Elem, Range, SolcRange},
    Edge, Node, NodeIdx,
};

use solang_parser::pt::{Expression, Loc};

impl<T> IntrinsicFuncCaller for T where
    T: AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike + Search
{
}
pub trait IntrinsicFuncCaller:
    AnalyzerLike<Expr = Expression, ExprErr = ExprErr> + Sized + GraphLike + Search
{
    /// Calls an intrinsic/builtin function call (casts, require, etc.)
    #[tracing::instrument(level = "trace", skip_all)]
    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        "abi.decode" => {
                            // we skip the first because that is what is being decoded.
                            // TODO: check if we have a concrete bytes value
                            fn match_decode(
                                ctx: ContextNode,
                                loc: &Loc,
                                ret: ExprRet,
                                analyzer: &mut impl AnalyzerLike,
                            ) -> Result<(), ExprErr> {
                                match ret {
                                    ExprRet::Single(expect_builtin) => {
                                        match analyzer.node(expect_builtin) {
                                            Node::Builtin(_) => {
                                                let var = ContextVar::new_from_builtin(
                                                    *loc,
                                                    expect_builtin.into(),
                                                    analyzer,
                                                )
                                                .into_expr_err(*loc)?;
                                                let node = analyzer.add_node(Node::ContextVar(var));
                                                ctx.add_var(node.into(), analyzer)
                                                    .into_expr_err(*loc)?;
                                                analyzer.add_edge(
                                                    node,
                                                    ctx,
                                                    Edge::Context(ContextEdge::Variable),
                                                );
                                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                                    .into_expr_err(*loc)?;
                                                Ok(())
                                            }
                                            Node::ContextVar(cvar) => {
                                                let bn = analyzer
                                                    .builtin_or_add(
                                                        cvar.ty
                                                            .as_builtin(analyzer)
                                                            .into_expr_err(*loc)?,
                                                    )
                                                    .into();
                                                let var = ContextVar::new_from_builtin(
                                                    *loc, bn, analyzer,
                                                )
                                                .into_expr_err(*loc)?;
                                                let node = analyzer.add_node(Node::ContextVar(var));
                                                ctx.add_var(node.into(), analyzer)
                                                    .into_expr_err(*loc)?;
                                                analyzer.add_edge(
                                                    node,
                                                    ctx,
                                                    Edge::Context(ContextEdge::Variable),
                                                );
                                                ctx.push_expr(ExprRet::Single(node), analyzer)
                                                    .into_expr_err(*loc)?;
                                                Ok(())
                                            }
                                            e => todo!("Unhandled type in abi.decode: {e:?}"),
                                        }
                                    }
                                    ExprRet::Multi(inner) => inner.iter().try_for_each(|i| {
                                        match_decode(ctx, loc, i.clone(), analyzer)
                                    }),
                                    ExprRet::CtxKilled(kind) => {
                                        ctx.kill(analyzer, *loc, kind).into_expr_err(*loc)
                                    }
                                    e => panic!("This is invalid solidity: {:?}", e),
                                }
                            }
                            self.parse_ctx_expr(&input_exprs[1], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "abi.decode was not given the types for decoding".to_string()))
                                };
                                if matches!(ret, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                match_decode(ctx, &loc, ret, analyzer)
                            })
                        }
                        "abi.encode"
                        | "abi.encodePacked"
                        | "abi.encodeCall"
                        | "abi.encodeWithSignature"
                        | "abi.encodeWithSelector" => {
                            // currently we dont support concrete abi encoding, TODO
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.push_expr(ExprRet::Single(node), self)
                                .into_expr_err(*loc)?;
                            Ok(())
                        }
                        "delegatecall" | "staticcall" | "call" => {
                            // TODO: try to be smarter based on the address input
                            let booln = self.builtin_or_add(Builtin::Bool);
                            let bool_cvar = ContextVar::new_from_builtin(*loc, booln.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(bool_cvar));
                            ctx.add_var(node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.push_expr(ExprRet::Single(node), self)
                                .into_expr_err(*loc)?;

                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.push_expr(ExprRet::Single(node), self)
                                .into_expr_err(*loc)?;
                            Ok(())
                        }
                        "code" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.push_expr(ExprRet::Single(node), self)
                                .into_expr_err(*loc)?;
                            Ok(())
                        }
                        "balance" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Uint(256));
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            ctx.add_var(node.into(), self).into_expr_err(*loc)?;
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ctx.push_expr(ExprRet::Single(node), self)
                                .into_expr_err(*loc)?;
                            Ok(())
                        }
                        "require" | "assert" => {
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, _loc| {
                                analyzer.handle_require(input_exprs, ctx)
                            })
                        }
                        "type" => self.parse_ctx_expr(&input_exprs[0], ctx),
                        "push" => {
                            assert!(input_exprs.len() == 2);
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoLhs(loc, "array[].push(..) was not an array to push to".to_string()))
                                };
                                if matches!(array, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                analyzer.parse_ctx_expr(&input_exprs[1], ctx)?;
                                analyzer.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
                                    let Some(new_elem) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                        return Err(ExprErr::NoRhs(loc, "array[].push(..) was not given an element to push".to_string()))
                                    };

                                    if matches!(new_elem, ExprRet::CtxKilled(_)) {
                                        ctx.push_expr(new_elem, analyzer).into_expr_err(loc)?;
                                        return Ok(());
                                    }

                                    let arr = array.expect_single().into_expr_err(loc)?;
                                    let arr = ContextVarNode::from(arr).latest_version(analyzer);
                                    // get length
                                    let len = analyzer.tmp_length(arr, ctx, loc);

                                    let len_as_idx = len.as_tmp(loc, ctx, analyzer).into_expr_err(loc)?;
                                    // set length as index
                                    analyzer.index_into_array_inner(
                                        ctx,
                                        loc,
                                        ExprRet::Single(arr.latest_version(analyzer).into()),
                                        ExprRet::Single(len_as_idx.latest_version(analyzer).into()),
                                    )?;
                                    let index = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?.unwrap();
                                    if matches!(index, ExprRet::CtxKilled(_)) {
                                        ctx.push_expr(index, analyzer).into_expr_err(loc)?;
                                        return Ok(());
                                    }
                                    // assign index to new_elem
                                    analyzer.match_assign_sides(ctx, loc, &index, &new_elem)
                                })
                            })
                        }
                        "pop" => {
                            assert!(input_exprs.len() == 1);
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(array) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoLhs(loc, "array[].pop() was not an array to pop from".to_string()))
                                };
                                if matches!(array, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(array, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }

                                // get the array
                                let arr = array.expect_single().into_expr_err(loc)?;
                                let arr = ContextVarNode::from(arr).latest_version(analyzer);

                                // get length
                                analyzer.match_length(ctx, loc, array, false)?;
                                let Some(len) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoLhs(loc, "array[].pop() was not an array to pop from".to_string()))
                                };
                                let len = len.expect_single().into_expr_err(loc)?;
                                let next_len = analyzer.advance_var_in_ctx(len.into(), loc, ctx)?;
                                next_len.set_range_min(analyzer, Elem::from(len) - Elem::from(Concrete::from(U256::from(1)))).into_expr_err(loc)?;
                                next_len.set_range_max(analyzer, Elem::from(len) - Elem::from(Concrete::from(U256::from(1)))).into_expr_err(loc)?;

                                // set length as index
                                analyzer.index_into_array_inner(
                                    ctx,
                                    loc,
                                    ExprRet::Single(arr.latest_version(analyzer).into()),
                                    ExprRet::Single(next_len.latest_version(analyzer).into()),
                                )
                            })
                        }
                        "concat" => self.concat(loc, input_exprs, ctx),
                        "keccak256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(_input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "abi.decode was not given the types for decoding".to_string()))
                                };
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer).into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "sha256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "abi.decode was not given the types for decoding".to_string()))
                                };
                                if matches!(input, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer).into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "ripemd160" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "abi.decode was not given the types for decoding".to_string()))
                                };
                                if matches!(input, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer).into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "blockhash" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "blockhash function was not provided a block number".to_string()))
                                };
                                if matches!(input, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Bytes(32)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer).into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "gasleft" => {
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Uint(64)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            ctx.push_expr(ExprRet::Single(cvar), self)
                                .into_expr_err(*loc)?;
                            Ok(())
                        }
                        "ecrecover" => {
                            input_exprs
                                .iter()
                                .try_for_each(|expr| self.parse_ctx_expr(expr, ctx))?;

                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                let cctx = Context::new_subctx(
                                        ctx,
                                        None,
                                        loc,
                                        None,
                                        Some(func_idx.into()),
                                        true,
                                        analyzer,
                                        None,
                                    )
                                    .into_expr_err(loc)?;
                                let call_ctx = analyzer.add_node(Node::Context(
                                    cctx
                                ));
                                ctx.set_child_call(call_ctx.into(), analyzer)
                                    .into_expr_err(loc)?;
                                let call_node = analyzer.add_node(Node::FunctionCall);
                                analyzer.add_edge(call_node, func_idx, Edge::Context(ContextEdge::Call));
                                analyzer.add_edge(call_node, ctx, Edge::Context(ContextEdge::Subcontext));
                                analyzer.add_edge(
                                    call_ctx,
                                    call_node,
                                    Edge::Context(ContextEdge::Subcontext),
                                );

                                let Some(input) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                                    return Err(ExprErr::NoRhs(loc, "ecrecover did not receive inputs".to_string()))
                                };

                                if matches!(input, ExprRet::CtxKilled(_)) {
                                    ctx.push_expr(input, analyzer).into_expr_err(loc)?;
                                    return Ok(());
                                }

                                let mut inner_vals = vec![];
                                match input {
                                    ExprRet::Single(var)
                                    | ExprRet::SingleLiteral(var) => {
                                        inner_vals.push(
                                            ContextVarNode::from(var).display_name(analyzer).unwrap(),
                                        );
                                    }
                                    _ => inner_vals.push("<unknown>".to_string()),
                                }
                                let inner_name = inner_vals.into_iter().collect::<Vec<_>>().join(", ");
                                let mut var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Address).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                var.display_name = format!("ecrecover({})", inner_name);
                                var.is_symbolic = true;
                                var.is_return = true;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.add_var(cvar.into(), analyzer).into_expr_err(loc)?;
                                analyzer.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Variable));
                                analyzer.add_edge(cvar, call_ctx, Edge::Context(ContextEdge::Return));
                                ContextNode::from(call_ctx)
                                    .add_return_node(loc, cvar.into(), analyzer)
                                    .into_expr_err(loc)?;

                                let rctx = Context::new_subctx(
                                        call_ctx.into(),
                                        Some(ctx),
                                        loc,
                                        None,
                                        None,
                                        true,
                                        analyzer,
                                        None,
                                    )
                                    .into_expr_err(loc)?;
                                let ret_ctx = analyzer.add_node(Node::Context(
                                    rctx
                                ));
                                ContextNode::from(call_ctx)
                                    .set_child_call(ret_ctx.into(), analyzer)
                                    .into_expr_err(loc)?;
                                analyzer.add_edge(ret_ctx, call_ctx, Edge::Context(ContextEdge::Continue));

                                let tmp_ret = ContextVarNode::from(cvar)
                                    .as_tmp(
                                        ContextNode::from(call_ctx).underlying(analyzer).unwrap().loc,
                                        ret_ctx.into(),
                                        analyzer,
                                    )
                                    .unwrap();
                                tmp_ret.underlying_mut(analyzer).unwrap().is_return = true;
                                tmp_ret.underlying_mut(analyzer).unwrap().display_name =
                                    format!("ecrecover({}).return", inner_name);
                                ctx.add_var(tmp_ret, analyzer).into_expr_err(loc)?;
                                analyzer.add_edge(tmp_ret, ret_ctx, Edge::Context(ContextEdge::Variable));

                                ContextNode::from(ret_ctx).push_expr(ExprRet::Single(tmp_ret.into()), analyzer).into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "addmod" => {
                            // TODO: actually calcuate this if possible
                            input_exprs
                                .iter()
                                .try_for_each(|expr| self.parse_ctx_expr(expr, ctx))?;

                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer)
                                    .into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        "mulmod" => {
                            // TODO: actually calcuate this if possible
                            input_exprs
                                .iter()
                                .try_for_each(|expr| self.parse_ctx_expr(expr, ctx))?;
                            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                                ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)?;
                                let var = ContextVar::new_from_builtin(
                                    loc,
                                    analyzer.builtin_or_add(Builtin::Uint(256)).into(),
                                    analyzer,
                                )
                                .into_expr_err(loc)?;
                                let cvar = analyzer.add_node(Node::ContextVar(var));
                                ctx.push_expr(ExprRet::Single(cvar), analyzer)
                                    .into_expr_err(loc)?;
                                Ok(())
                            })
                        }
                        e => Err(ExprErr::Todo(
                            *loc,
                            format!("builtin function: {e:?} doesn't exist or isn't implemented"),
                        )),
                    }
                } else {
                    panic!("unnamed builtin?")
                }
            }
            Node::Builtin(Builtin::Array(_)) => {
                // create a new list
                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(len_var) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Array creation failed".to_string()))
                    };

                    if matches!(len_var, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(len_var, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let len_cvar = len_var.expect_single().into_expr_err(loc)?;

                    let ty = VarType::try_from_idx(analyzer, func_idx);

                    let new_arr = ContextVar {
                        loc: Some(loc),
                        name: format!("tmp_arr{}", ctx.new_tmp(analyzer).into_expr_err(loc)?),
                        display_name: "arr".to_string(),
                        storage: None,
                        is_tmp: true,
                        is_symbolic: false,
                        is_return: false,
                        tmp_of: None,
                        ty: ty.expect("No type for node"),
                    };

                    let arr = ContextVarNode::from(analyzer.add_node(Node::ContextVar(new_arr)));

                    let len_var = ContextVar {
                        loc: Some(loc),
                        name: arr.name(analyzer).into_expr_err(loc)? + ".length",
                        display_name: arr.display_name(analyzer).unwrap() + ".length",
                        storage: None,
                        is_tmp: true,
                        tmp_of: None,
                        is_symbolic: true,
                        is_return: false,
                        ty: ContextVarNode::from(len_cvar)
                            .underlying(analyzer)
                            .into_expr_err(loc)?
                            .ty
                            .clone(),
                    };

                    let len_cvar = analyzer.add_node(Node::ContextVar(len_var));
                    analyzer.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(arr, analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(len_cvar.into(), analyzer).into_expr_err(loc)?;
                    analyzer.add_edge(len_cvar, arr, Edge::Context(ContextEdge::AttrAccess));

                    // update the length
                    if let Some(r) = arr.ref_range(analyzer).into_expr_err(loc)? {
                        let min = r.evaled_range_min(analyzer).into_expr_err(loc)?;
                        let max = r.evaled_range_max(analyzer).into_expr_err(loc)?;

                        if let Some(mut rd) = min.maybe_range_dyn() {
                            rd.len = Elem::from(len_cvar);
                            arr.set_range_min(analyzer, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc)?;
                        }

                        if let Some(mut rd) = max.maybe_range_dyn() {
                            rd.len = Elem::from(len_cvar);
                            arr.set_range_min(analyzer, Elem::ConcreteDyn(Box::new(rd)))
                                .into_expr_err(loc)?;
                        }
                    }

                    ctx.push_expr(ExprRet::Single(arr.into()), analyzer)
                        .into_expr_err(loc)?;
                    Ok(())
                })
            }
            Node::Builtin(ty) => {
                // it is a cast
                let ty = ty.clone();
                fn cast_match(
                    ctx: ContextNode,
                    loc: Loc,
                    analyzer: &mut (impl GraphLike + AnalyzerLike),
                    ty: &Builtin,
                    ret: ExprRet,
                    func_idx: NodeIdx,
                ) -> Result<(), ExprErr> {
                    match ret {
                        ExprRet::CtxKilled(kind) => {
                            ctx.kill(analyzer, loc, kind).into_expr_err(loc)
                        }
                        ExprRet::Null => Ok(()),
                        ExprRet::Single(cvar) | ExprRet::SingleLiteral(cvar) => {
                            let new_var = ContextVarNode::from(cvar)
                                .as_cast_tmp(loc, ctx, ty.clone(), analyzer)
                                .into_expr_err(loc)?;

                            new_var.underlying_mut(analyzer).into_expr_err(loc)?.ty =
                                VarType::try_from_idx(analyzer, func_idx).expect("");
                            // cast the ranges
                            if let Some(r) = ContextVarNode::from(cvar)
                                .range(analyzer)
                                .into_expr_err(loc)?
                            {
                                let curr_range =
                                    SolcRange::try_from_builtin(ty).expect("No default range");
                                let min = r
                                    .range_min()
                                    .into_owned()
                                    .cast(curr_range.range_min().into_owned());
                                let max = r
                                    .range_max()
                                    .into_owned()
                                    .cast(curr_range.range_max().into_owned());
                                new_var.set_range_min(analyzer, min).into_expr_err(loc)?;
                                new_var.set_range_max(analyzer, max).into_expr_err(loc)?;
                                // cast the range exclusions - TODO: verify this is correct
                                let mut exclusions = r.range_exclusions();
                                exclusions.iter_mut().for_each(|range| {
                                    *range =
                                        range.clone().cast(curr_range.range_min().into_owned());
                                });
                                new_var
                                    .set_range_exclusions(analyzer, exclusions)
                                    .into_expr_err(loc)?;
                            }

                            ctx.push_expr(ExprRet::Single(new_var.into()), analyzer)
                                .into_expr_err(loc)?;
                            Ok(())
                        }
                        ExprRet::Multi(inner) => inner
                            .into_iter()
                            .try_for_each(|i| cast_match(ctx, loc, analyzer, ty, i, func_idx)),
                    }
                }

                self.parse_ctx_expr(&input_exprs[0], ctx)?;
                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Array creation failed".to_string()))
                    };

                    if matches!(ret, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }

                    cast_match(ctx, loc, analyzer, &ty, ret, func_idx)
                })
            }
            Node::ContextVar(_c) => {
                // its a user type
                // TODO: figure out if we actually need to do anything?
                // input_exprs
                //     .iter()
                //     .try_for_each(|expr| self.parse_ctx_expr(expr, ctx))?;

                // self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                // })

                ctx.push_expr(ExprRet::Single(func_idx), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            Node::Contract(_) => {
                // TODO: figure out if we need to do anything
                // let _inputs: Vec<_> = input_exprs
                //     .iter()
                //     .map(|expr| self.parse_ctx_expr(expr, ctx))
                //     .collect();

                ctx.push_expr(ExprRet::Single(func_idx), self)
                    .into_expr_err(*loc)?;
                Ok(())
            }
            Node::Unresolved(_) => {
                input_exprs
                    .iter()
                    .try_for_each(|expr| self.parse_ctx_expr(expr, ctx))?;

                self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                    let Some(inputs) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                        return Err(ExprErr::NoRhs(loc, "Function call failed".to_string()))
                    };

                    if matches!(inputs, ExprRet::CtxKilled(_)) {
                        ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                        return Ok(());
                    }
                    let visible_funcs = ctx.visible_funcs(analyzer).into_expr_err(loc)?
                                    .iter()
                                    .map(|func| func.name(analyzer).unwrap())
                                    .collect::<Vec<_>>();

                    if let Node::Unresolved(ident) = analyzer.node(func_idx) {
                        Err(ExprErr::FunctionNotFound(
                            loc,
                            format!(
                                "Could not find function: \"{}{}\", context: {}, visible functions: {:#?}",
                                ident.name,
                                inputs.try_as_func_input_str(analyzer),
                                ctx.path(analyzer),
                                visible_funcs
                            )
                        ))
                    } else {
                        unreachable!()
                    }
                })
            }
            e => Err(ExprErr::FunctionNotFound(*loc, format!("{e:?}"))),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn concat(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        input_exprs[1..].iter().try_for_each(|expr| {
            self.parse_ctx_expr(expr, ctx)?;
            self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
                let input = ctx
                    .pop_expr_latest(loc, analyzer)
                    .into_expr_err(loc)?
                    .unwrap_or(ExprRet::Null);
                ctx.append_tmp_expr(input, analyzer).into_expr_err(loc)
            })
        })?;

        self.apply_to_edges(ctx, *loc, &|analyzer, ctx, loc| {
            let Some(inputs) = ctx.pop_tmp_expr(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "Concatenation failed".to_string()))
            };
            println!("inputs: {inputs:?}");
            if matches!(inputs, ExprRet::CtxKilled(_)) {
                ctx.push_expr(inputs, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            let inputs = inputs.as_vec();
            if inputs.is_empty() {
                ctx.push_expr(ExprRet::Multi(vec![]), analyzer)
                    .into_expr_err(loc)?;
                Ok(())
            } else {
                let start = &inputs[0];
                if inputs.len() > 1 {
                    analyzer.match_concat(ctx, loc, start.clone(), &inputs[1..], None)
                } else {
                    analyzer.match_concat(ctx, loc, start.clone(), &[], None)
                }
            }
        })
    }

    fn match_concat(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        curr: ExprRet,
        inputs: &[ExprRet],
        accum_node: Option<ContextVarNode>,
    ) -> Result<(), ExprErr> {
        if let Some(accum_node) = accum_node {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    self.concat_inner(loc, accum_node, ContextVarNode::from(var))?;
                    ctx.push_expr(ExprRet::Single(accum_node.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Null => {
                    ctx.push_expr(ExprRet::Single(accum_node.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, Some(accum_node))),
                ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            }
        } else {
            match curr.flatten() {
                ExprRet::Single(var) | ExprRet::SingleLiteral(var) => {
                    let acc = ContextVarNode::from(var)
                        .as_tmp(loc, ctx, self)
                        .into_expr_err(loc)?;
                    inputs
                        .iter()
                        .map(|i| self.match_concat(ctx, loc, i.clone(), inputs, Some(acc)))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    ctx.push_expr(ExprRet::Single(acc.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
                ExprRet::Null => Err(ExprErr::NoRhs(
                    loc,
                    "No input provided to concat function".to_string(),
                )),
                ExprRet::Multi(inner) => inner
                    .into_iter()
                    .try_for_each(|i| self.match_concat(ctx, loc, i, inputs, None)),
                ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            }
        }
    }

    fn concat_inner(
        &mut self,
        loc: Loc,
        accum: ContextVarNode,
        right: ContextVarNode,
    ) -> Result<(), ExprErr> {
        match (
            accum.ty(self).into_expr_err(loc)?,
            right.ty(self).into_expr_err(loc)?,
        ) {
            (VarType::Concrete(accum_cnode), VarType::Concrete(right_cnode)) => {
                let new_ty = match (
                    accum_cnode.underlying(self).into_expr_err(loc)?,
                    right_cnode.underlying(self).into_expr_err(loc)?,
                ) {
                    (accum_node @ Concrete::String(..), right_node @ Concrete::String(..)) => {
                        let new_val = accum_node.clone().concat(right_node).unwrap();
                        let new_cnode = self.add_node(Node::Concrete(new_val));
                        VarType::Concrete(new_cnode.into())
                    }
                    (accum_node @ Concrete::DynBytes(..), right_node @ Concrete::DynBytes(..)) => {
                        let new_val = accum_node.clone().concat(right_node).unwrap();
                        let new_cnode = self.add_node(Node::Concrete(new_val));
                        VarType::Concrete(new_cnode.into())
                    }
                    (a, b) => {
                        // Invalid solidity
                        return Err(ExprErr::InvalidFunctionInput(loc, format!("Type mismatch: {a:?} for left hand side and type: {b:?} for right hand side")));
                    }
                };
                accum.underlying_mut(self).into_expr_err(loc)?.ty = new_ty;
                Ok(())
            }
            (VarType::Concrete(accum_cnode), VarType::BuiltIn(_bn, Some(r2))) => {
                let underlying = accum_cnode.underlying(self).into_expr_err(loc)?;
                // let val = match underlying {
                //     Concrete::String(val) => {
                //         val
                //             .chars()
                //             .enumerate()
                //             .map(|(i, v)| {
                //                 let idx = Elem::from(Concrete::from(U256::from(i)));
                //                 let mut bytes = [0x00; 32];
                //                 v.encode_utf8(&mut bytes[..]);
                //                 let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                //                 (idx, v)
                //             })
                //             .collect::<BTreeMap<_, _>>()
                //     }
                //     Concrete::DynBytes(val) => {
                //         val
                //             .iter()
                //             .enumerate()
                //             .map(|(i, v)| {
                //                 let idx = Elem::from(Concrete::from(U256::from(i)));
                //                 let mut bytes = [0x00; 32];
                //                 bytes[0] = *v;
                //                 let v = Elem::from(Concrete::Bytes(1, H256::from(bytes)));
                //                 (idx, v)
                //             })
                //             .collect::<BTreeMap<_, _>>()
                //     }
                //     b => return Err(ExprErr::InvalidFunctionInput(loc, format!("Type mismatch: expected String or Bytes for concat input but found: {b:?}")))
                // };
                // TODO: Extend with bn

                let range = SolcRange::from(underlying.clone()).unwrap();
                let min = range.min.clone().concat(r2.min.clone());
                let max = range.max.clone().concat(r2.max.clone());
                accum.set_range_min(self, min).into_expr_err(loc)?;
                accum.set_range_max(self, max).into_expr_err(loc)?;

                let new_ty =
                    VarType::BuiltIn(self.builtin_or_add(Builtin::String).into(), Some(range));
                accum.underlying_mut(self).into_expr_err(loc)?.ty = new_ty;
                Ok(())
            }
            (VarType::BuiltIn(_bn, Some(r)), VarType::BuiltIn(_bn2, Some(r2))) => {
                // TODO: improve length calculation here
                let min = r.min.clone().concat(r2.min.clone());
                let max = r.max.clone().concat(r2.max.clone());
                accum.set_range_min(self, min).into_expr_err(loc)?;
                accum.set_range_max(self, max).into_expr_err(loc)?;
                Ok(())
            }
            (_, _) => Ok(()),
        }
    }
}
