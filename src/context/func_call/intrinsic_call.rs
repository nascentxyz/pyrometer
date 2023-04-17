use crate::context::{ExprErr, IntoExprErr};
use crate::{
    context::{
        exprs::{Array, MemberAccess, Require},
        ContextBuilder,
    },
    ExprRet,
};
use ethers_core::types::H256;
use ethers_core::types::U256;
use shared::analyzer::Search;
use shared::analyzer::{AnalyzerLike, GraphLike};
use shared::nodes::Concrete;
use shared::range::elem_ty::RangeDyn;
use shared::{
    context::*,
    nodes::{Builtin, VarType},
    range::{
        elem_ty::{Dynamic, Elem},
        Range, SolcRange,
    },
    Edge, Node, NodeIdx,
};
use std::collections::BTreeMap;
use std::collections::VecDeque;

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
    ) -> Result<ExprRet, ExprErr> {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        "abi.decode" => {
                            // we skip the first because that is what is being decoded.
                            // TODO: check if we have a concrete bytes value
                            let ret = self.parse_ctx_expr(&input_exprs[1], ctx)?;
                            fn match_decode(
                                loc: &Loc,
                                ret: ExprRet,
                                analyzer: &mut impl AnalyzerLike,
                            ) -> Result<ExprRet, ExprErr> {
                                let res = match ret {
                                    ExprRet::Single((ctx, expect_builtin)) => {
                                        match analyzer.node(expect_builtin) {
                                            Node::Builtin(_) => {
                                                let var = ContextVar::new_from_builtin(
                                                    *loc,
                                                    expect_builtin.into(),
                                                    analyzer,
                                                )
                                                .into_expr_err(*loc)?;
                                                let node = analyzer.add_node(Node::ContextVar(var));
                                                analyzer.add_edge(
                                                    node,
                                                    ctx,
                                                    Edge::Context(ContextEdge::Variable),
                                                );
                                                ExprRet::Single((ctx, node))
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
                                                analyzer.add_edge(
                                                    node,
                                                    ctx,
                                                    Edge::Context(ContextEdge::Variable),
                                                );
                                                ExprRet::Single((ctx, node))
                                            }
                                            e => todo!("Unhandled type in abi.decode: {e:?}"),
                                        }
                                    }
                                    ExprRet::Multi(inner) => ExprRet::Multi(
                                        inner
                                            .iter()
                                            .map(|i| match_decode(loc, i.clone(), analyzer))
                                            .collect::<Result<Vec<_>, _>>()?,
                                    ),
                                    e => panic!("This is invalid solidity: {:?}", e),
                                };
                                Ok(res)
                            }
                            match_decode(loc, ret, self)
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
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "delegatecall" | "staticcall" | "call" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "code" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "balance" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::Uint(256));
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self)
                                .into_expr_err(*loc)?;
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            Ok(ExprRet::Single((ctx, node)))
                        }
                        "require" | "assert" => {
                            self.handle_require(input_exprs, ctx)?;
                            Ok(ExprRet::Multi(vec![]))
                        }
                        "type" => Ok(ExprRet::Single(
                            self.parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?,
                        )),
                        "push" => {
                            assert!(input_exprs.len() == 2);
                            let (arr_ctx, arr) = self
                                .parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?;
                            let arr = ContextVarNode::from(arr).latest_version(self);
                            // get length
                            let len = self.tmp_length(arr, arr_ctx, *loc);

                            let len_as_idx = len.as_tmp(*loc, ctx, self).into_expr_err(*loc)?;
                            // set length as index
                            let index = self.index_into_array_inner(
                                *loc,
                                ExprRet::Single((arr_ctx, arr.latest_version(self).into())),
                                ExprRet::Single((arr_ctx, len_as_idx.latest_version(self).into())),
                            )?;
                            // assign index to new_elem
                            let new_elem = self.parse_ctx_expr(&input_exprs[1], ctx)?;
                            self.match_assign_sides(*loc, &index, &new_elem)
                        }
                        "concat" => self.concat(loc, input_exprs, ctx),
                        "keccak256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?;
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(32)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "sha256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?;
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(32)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "ripemd160" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?;
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(20)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "blockhash" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx)?
                                .expect_single(*loc)?;
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(32)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "gasleft" => {
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Uint(64)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "ecrecover" => {
                            for expr in input_exprs.iter() {
                                // we want to parse even though we dont need the variables here
                                let _ = self.parse_ctx_expr(expr, ctx)?;
                            }
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Address).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "addmod" => {
                            // TODO: actually calcuate this if possible
                            for expr in input_exprs.iter() {
                                let _ = self.parse_ctx_expr(expr, ctx)?;
                            }
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Uint(256)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
                        }
                        "mulmod" => {
                            // TODO: actually calcuate this if possible
                            for expr in input_exprs.iter() {
                                let _ = self.parse_ctx_expr(expr, ctx)?;
                            }
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Uint(256)).into(),
                                self,
                            )
                            .into_expr_err(*loc)?;
                            let cvar = self.add_node(Node::ContextVar(var));
                            Ok(ExprRet::Single((ctx, cvar)))
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
                let (ctx, len_cvar) = self
                    .parse_ctx_expr(&input_exprs[0], ctx)?
                    .expect_single(*loc)?;
                let ty = VarType::try_from_idx(self, func_idx);

                let new_arr = ContextVar {
                    loc: Some(*loc),
                    name: format!("tmp_arr{}", ctx.new_tmp(self).into_expr_err(*loc)?),
                    display_name: "arr".to_string(),
                    storage: None,
                    is_tmp: true,
                    is_symbolic: false,
                    tmp_of: None,
                    ty: ty.expect("No type for node"),
                };

                let arr = ContextVarNode::from(self.add_node(Node::ContextVar(new_arr)));

                let len_var = ContextVar {
                    loc: Some(*loc),
                    name: arr.name(self).into_expr_err(*loc)? + ".length",
                    display_name: arr.display_name(self).unwrap() + ".length",
                    storage: None,
                    is_tmp: true,
                    tmp_of: None,
                    is_symbolic: true,
                    ty: ContextVarNode::from(len_cvar)
                        .underlying(self)
                        .into_expr_err(*loc)?
                        .ty
                        .clone(),
                };

                let len_cvar = self.add_node(Node::ContextVar(len_var));
                self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, arr, Edge::Context(ContextEdge::AttrAccess));

                // update the length
                if let Some(r) = arr.range(self).into_expr_err(*loc)? {
                    let min = r.evaled_range_min(self).into_expr_err(*loc)?;
                    let max = r.evaled_range_max(self).into_expr_err(*loc)?;

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(*loc)?;
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(*loc)?;
                    }
                }

                Ok(ExprRet::Single((ctx, arr.into())))
            }
            Node::Builtin(ty) => {
                // it is a cast
                let ty = ty.clone();
                fn cast_match(
                    loc: &Loc,
                    analyzer: &mut (impl GraphLike + AnalyzerLike),
                    ty: Builtin,
                    ret: ExprRet,
                    func_idx: NodeIdx,
                ) -> Result<ExprRet, ExprErr> {
                    let res = match ret {
                        ExprRet::CtxKilled => ExprRet::CtxKilled,
                        ExprRet::Single((ctx, cvar)) | ExprRet::SingleLiteral((ctx, cvar)) => {
                            let new_var = ContextVarNode::from(cvar)
                                .as_cast_tmp(*loc, ctx, ty.clone(), analyzer)
                                .into_expr_err(*loc)?;

                            new_var.underlying_mut(analyzer).into_expr_err(*loc)?.ty =
                                VarType::try_from_idx(analyzer, func_idx).expect("");
                            // cast the ranges
                            if let Some(r) = ContextVarNode::from(cvar)
                                .range(analyzer)
                                .into_expr_err(*loc)?
                            {
                                let curr_range =
                                    SolcRange::try_from_builtin(&ty).expect("No default range");
                                new_var
                                    .set_range_min(
                                        analyzer,
                                        r.range_min().cast(curr_range.range_min()),
                                    )
                                    .into_expr_err(*loc)?;
                                new_var
                                    .set_range_max(
                                        analyzer,
                                        r.range_max().cast(curr_range.range_max()),
                                    )
                                    .into_expr_err(*loc)?;
                                // cast the range exclusions - TODO: verify this is correct
                                let mut exclusions = r.range_exclusions();
                                exclusions.iter_mut().for_each(|range| {
                                    *range = range.clone().cast(curr_range.range_min());
                                });
                                new_var
                                    .set_range_exclusions(analyzer, exclusions)
                                    .into_expr_err(*loc)?;
                            }

                            ExprRet::Single((ctx, new_var.into()))
                        }
                        ExprRet::Multi(inner) => ExprRet::Multi(
                            inner
                                .into_iter()
                                .map(|i| cast_match(loc, analyzer, ty.clone(), i, func_idx))
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        ExprRet::Fork(w1, w2) => ExprRet::Fork(
                            Box::new(cast_match(loc, analyzer, ty.clone(), *w1, func_idx)?),
                            Box::new(cast_match(loc, analyzer, ty, *w2, func_idx)?),
                        ),
                    };
                    Ok(res)
                }

                let ret = self.parse_ctx_expr(&input_exprs[0], ctx)?.flatten();
                cast_match(loc, self, ty, ret, func_idx)
            }
            Node::ContextVar(_c) => {
                // its a user type
                // TODO: figure out if we actually need to do anything?
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                Ok(ExprRet::Single((ctx, func_idx)))
            }
            Node::Contract(_) => {
                // TODO: figure out if we need to do anything
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                Ok(ExprRet::Single((ctx, func_idx)))
            }
            Node::Unresolved(_) => {
                let inputs = ExprRet::Multi(
                    input_exprs
                        .iter()
                        .map(|expr| self.parse_ctx_expr(expr, ctx))
                        .collect::<Result<Vec<_>, ExprErr>>()?,
                );
                if let Node::Unresolved(ident) = self.node(func_idx) {
                    Err(ExprErr::FunctionNotFound(
                        *loc,
                        format!(
                            "Could not find function: \"{}{}\"",
                            ident.name,
                            inputs.try_as_func_input_str(self)
                        ),
                    ))
                } else {
                    unreachable!()
                }
            }
            e => Err(ExprErr::FunctionNotFound(*loc, format!("{e:?}"))),
        }
    }

    fn concat(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        ctx: ContextNode,
    ) -> Result<ExprRet, ExprErr> {
        let inputs = input_exprs[1..]
            .iter()
            .map(|expr| self.parse_ctx_expr(expr, ctx))
            .collect::<Result<Vec<_>, ExprErr>>()?;

        if inputs.is_empty() {
            Ok(ExprRet::Multi(vec![]))
        } else {
            let start = &inputs[0];
            if inputs.len() > 1 {
                self.match_concat(ctx, loc, start.clone(), &inputs[1..], None)
            } else {
                self.match_concat(ctx, loc, start.clone(), &[], None)
            }
        }
    }

    fn match_concat(
        &mut self,
        ctx: ContextNode,
        loc: &Loc,
        curr: ExprRet,
        inputs: &[ExprRet],
        accum_node: Option<ContextVarNode>,
    ) -> Result<ExprRet, ExprErr> {
        if let Some(accum_node) = accum_node {
            match curr.flatten() {
                ExprRet::Single((ctx, var)) | ExprRet::SingleLiteral((ctx, var)) => {
                    self.concat_inner(*loc, accum_node, ContextVarNode::from(var))?;
                    Ok(ExprRet::Single((ctx, accum_node.into())))
                }
                ExprRet::Multi(inner) => {
                    inner
                        .into_iter()
                        .map(|i| self.match_concat(ctx, loc, i, inputs, Some(accum_node)))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    Ok(ExprRet::Single((ctx, accum_node.into())))
                }
                ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                    Box::new(self.match_concat(ctx, loc, *w1, inputs, Some(accum_node))?),
                    Box::new(self.match_concat(ctx, loc, *w2, inputs, Some(accum_node))?),
                )),
                ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
            }
        } else {
            match curr.flatten() {
                ExprRet::Single((ctx, var)) | ExprRet::SingleLiteral((ctx, var)) => {
                    let acc = ContextVarNode::from(var)
                        .as_tmp(*loc, ctx, self)
                        .into_expr_err(*loc)?;
                    inputs
                        .iter()
                        .map(|i| self.match_concat(ctx, loc, i.clone(), inputs, Some(acc)))
                        .collect::<Result<Vec<_>, ExprErr>>()?;
                    Ok(ExprRet::Single((ctx, acc.into())))
                }
                ExprRet::Multi(inner) => Ok(ExprRet::Multi(
                    inner
                        .into_iter()
                        .map(|i| self.match_concat(ctx, loc, i, inputs, None))
                        .collect::<Result<Vec<_>, ExprErr>>()?,
                )),
                ExprRet::Fork(w1, w2) => Ok(ExprRet::Fork(
                    Box::new(self.match_concat(ctx, loc, *w1, inputs, None)?),
                    Box::new(self.match_concat(ctx, loc, *w2, inputs, None)?),
                )),
                ExprRet::CtxKilled => Ok(ExprRet::CtxKilled),
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
