use crate::{
    context::{
        exprs::{Array, MemberAccess, Require},
        ContextBuilder,
    },
    ExprRet,
};
use shared::{
    analyzer::{AnalyzerLike, GraphLike},
    context::*,
    nodes::{Builtin, VarType},
    range::{
        elem_ty::{Dynamic, Elem},
        Range, SolcRange,
    },
    Edge, Node, NodeIdx,
};

use solang_parser::pt::{Expression, Loc};

impl<T> IntrinsicFuncCaller for T where T: AnalyzerLike<Expr = Expression> + Sized + GraphLike {}
pub trait IntrinsicFuncCaller: AnalyzerLike<Expr = Expression> + Sized + GraphLike {
    /// Calls an intrinsic/builtin function call (casts, require, etc.)
    #[tracing::instrument(level = "trace", skip_all)]
    fn intrinsic_func_call(
        &mut self,
        loc: &Loc,
        input_exprs: &[Expression],
        func_idx: NodeIdx,
        ctx: ContextNode,
    ) -> ExprRet {
        match self.node(func_idx) {
            Node::Function(underlying) => {
                if let Some(func_name) = &underlying.name {
                    match &*func_name.name {
                        "abi.decode" => {
                            // we skip the first because that is what is being decoded.
                            // TODO: check if we have a concrete bytes value
                            let ret = self.parse_ctx_expr(&input_exprs[1], ctx);
                            fn match_decode(
                                loc: &Loc,
                                ret: ExprRet,
                                analyzer: &mut (impl GraphLike + AnalyzerLike),
                            ) -> ExprRet {
                                match ret {
                                    ExprRet::Single((ctx, expect_builtin)) => {
                                        match analyzer.node(expect_builtin) {
                                            Node::Builtin(_) => {
                                                let var = ContextVar::new_from_builtin(
                                                    *loc,
                                                    expect_builtin.into(),
                                                    analyzer,
                                                );
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
                                                    .builtin_or_add(cvar.ty.as_builtin(analyzer))
                                                    .into();
                                                let var = ContextVar::new_from_builtin(
                                                    *loc, bn, analyzer,
                                                );
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
                                            .collect(),
                                    ),
                                    e => panic!("This is invalid solidity: {:?}", e),
                                }
                            }
                            match_decode(loc, ret, self)
                        }
                        "abi.encode"
                        | "abi.encodePacked"
                        | "abi.encodeCall"
                        | "abi.encodeWithSignature" => {
                            // currently we dont support concrete abi encoding, TODO
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self);
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ExprRet::Single((ctx, node))
                        }
                        "delegatecall" | "staticcall" | "call" => {
                            // TODO: try to be smarter based on the address input
                            let bn = self.builtin_or_add(Builtin::DynamicBytes);
                            let cvar = ContextVar::new_from_builtin(*loc, bn.into(), self);
                            let node = self.add_node(Node::ContextVar(cvar));
                            self.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
                            ExprRet::Single((ctx, node))
                        }
                        "require" | "assert" => {
                            self.handle_require(input_exprs, ctx);
                            ExprRet::Multi(vec![])
                        }
                        "type" => ExprRet::Single(
                            self.parse_ctx_expr(&input_exprs[0], ctx).expect_single(),
                        ),
                        "push" => {
                            assert!(input_exprs.len() == 2);
                            let (arr_ctx, arr) =
                                self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                            let arr = ContextVarNode::from(arr).latest_version(self);
                            // get length
                            let len = self.tmp_length(arr, arr_ctx, *loc);

                            let len_as_idx = len.as_tmp(*loc, ctx, self);
                            // set length as index
                            let index = self.index_into_array_inner(
                                *loc,
                                ExprRet::Single((arr_ctx, arr.latest_version(self).into())),
                                ExprRet::Single((arr_ctx, len_as_idx.latest_version(self).into())),
                            );
                            // assign index to new_elem
                            let new_elem = self.parse_ctx_expr(&input_exprs[1], ctx);
                            self.match_assign_sides(*loc, &index, &new_elem)
                        }
                        "keccak256" => {
                            self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Bytes(32)).into(),
                                self,
                            );
                            let cvar = self.add_node(Node::ContextVar(var));
                            ExprRet::Single((ctx, cvar))
                        }
                        "ecrecover" => {
                            input_exprs.iter().for_each(|expr| {
                                // we want to parse even though we dont need the variables here
                                let _ = self.parse_ctx_expr(expr, ctx);
                            });
                            let var = ContextVar::new_from_builtin(
                                *loc,
                                self.builtin_or_add(Builtin::Address).into(),
                                self,
                            );
                            let cvar = self.add_node(Node::ContextVar(var));
                            ExprRet::Single((ctx, cvar))
                        }
                        e => todo!("builtin function: {:?}", e),
                    }
                } else {
                    panic!("unnamed builtin?")
                }
            }
            Node::Builtin(Builtin::Array(_)) => {
                // create a new list
                let (ctx, len_cvar) = self.parse_ctx_expr(&input_exprs[0], ctx).expect_single();
                let ty = VarType::try_from_idx(self, func_idx);

                let new_arr = ContextVar {
                    loc: Some(*loc),
                    name: format!("tmp_arr{}", ctx.new_tmp(self)),
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
                    name: arr.name(self) + ".length",
                    display_name: arr.display_name(self) + ".length",
                    storage: None,
                    is_tmp: true,
                    tmp_of: None,
                    is_symbolic: true,
                    ty: ContextVarNode::from(len_cvar).underlying(self).ty.clone(),
                };

                let len_cvar = self.add_node(Node::ContextVar(len_var));
                self.add_edge(arr, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, ctx, Edge::Context(ContextEdge::Variable));
                self.add_edge(len_cvar, arr, Edge::Context(ContextEdge::AttrAccess));

                // update the length
                if let Some(r) = arr.range(self) {
                    let min = r.evaled_range_min(self);
                    let max = r.evaled_range_max(self);

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)));
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::Dynamic(Dynamic::new(len_cvar, *loc));
                        arr.set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                    }
                }

                ExprRet::Single((ctx, arr.into()))
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
                ) -> ExprRet {
                    match ret {
                        ExprRet::CtxKilled => ExprRet::CtxKilled,
                        ExprRet::Single((ctx, cvar)) | ExprRet::SingleLiteral((ctx, cvar)) => {
                            let new_var = ContextVarNode::from(cvar).as_cast_tmp(
                                *loc,
                                ctx,
                                ty.clone(),
                                analyzer,
                            );

                            new_var.underlying_mut(analyzer).ty =
                                VarType::try_from_idx(analyzer, func_idx).expect("");
                            // cast the ranges
                            if let Some(r) = ContextVarNode::from(cvar).range(analyzer) {
                                let curr_range =
                                    SolcRange::try_from_builtin(&ty).expect("No default range");
                                new_var.set_range_min(
                                    analyzer,
                                    r.range_min().cast(curr_range.range_min()),
                                );
                                new_var.set_range_max(
                                    analyzer,
                                    r.range_max().cast(curr_range.range_max()),
                                );
                                // cast the range exclusions - TODO: verify this is correct
                                let mut exclusions = r.range_exclusions();
                                exclusions.iter_mut().for_each(|range| {
                                    *range = range.clone().cast(curr_range.range_min());
                                });
                                new_var.set_range_exclusions(analyzer, exclusions);
                            }

                            ExprRet::Single((ctx, new_var.into()))
                        }
                        ExprRet::Multi(inner) => ExprRet::Multi(
                            inner
                                .into_iter()
                                .map(|i| cast_match(loc, analyzer, ty.clone(), i, func_idx))
                                .collect(),
                        ),
                        ExprRet::Fork(w1, w2) => ExprRet::Fork(
                            Box::new(cast_match(loc, analyzer, ty.clone(), *w1, func_idx)),
                            Box::new(cast_match(loc, analyzer, ty, *w2, func_idx)),
                        ),
                    }
                }

                let ret = self.parse_ctx_expr(&input_exprs[0], ctx).flatten();
                cast_match(loc, self, ty, ret, func_idx)
            }
            Node::ContextVar(_c) => {
                // its a user type
                // TODO: figure out if we actually need to do anything?
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            Node::Contract(_) => {
                // TODO: figure out if we need to do anything
                let _inputs: Vec<_> = input_exprs
                    .iter()
                    .map(|expr| self.parse_ctx_expr(expr, ctx))
                    .collect();

                ExprRet::Single((ctx, func_idx))
            }
            e => todo!("{:?}", e),
        }
    }
}
