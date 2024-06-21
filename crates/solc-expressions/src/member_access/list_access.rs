use crate::{ContextBuilder, ExprErr, ExpressionParser, IntoExprErr, Variable};

use graph::{
    elem::*,
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, Range, SolcRange, VarType,
};
use shared::RangeArena;

use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> ListAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles list/array member access (indices, length, etc)
pub trait ListAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        loc: Loc,
        input_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(arena, input_expr, ctx)?;
        self.apply_to_edges(ctx, loc, arena, &|analyzer, arena, ctx, loc| {
            let Some(ret) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoLhs(
                    loc,
                    "Attempted to perform member access without a left-hand side".to_string(),
                ));
            };
            if matches!(ret, ExprRet::CtxKilled(_)) {
                ctx.push_expr(ret, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_length(arena, ctx, loc, ret, true)
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn match_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        elem_path: ExprRet,
        _update_len_bound: bool,
    ) -> Result<(), ExprErr> {
        match elem_path {
            ExprRet::Null => {
                ctx.push_expr(ExprRet::Null, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(arr) => {
                self.get_length(arena, ctx, loc, arr.into(), false)?;
                Ok(())
            }
            e => todo!("here: {e:?}"),
        }
    }

    fn get_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        array: ContextVarNode,
        return_var: bool,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        let next_arr = self.advance_var_in_ctx(array.latest_version(self), loc, ctx)?;
        // search for latest length
        if let Some(len_var) = next_arr.array_to_len_var(self) {
            let len_node = self.advance_var_in_ctx(len_var.latest_version(self), loc, ctx)?;
            if !return_var {
                ctx.push_expr(ExprRet::Single(len_node.into()), self)
                    .into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(len_node))
            }
        } else {
            self.create_length(arena, ctx, loc, array, next_arr, return_var)
            // no length variable, create one
            // let name = format!("{}.length", array.name(self).into_expr_err(loc)?);

            // // Create the range from the current length or default to [0, uint256.max]

            // let len_min = Elem::from(next_arr)
            //     .get_length()
            //     .max(Elem::from(Concrete::from(U256::zero())));
            // let len_max = Elem::from(next_arr)
            //     .get_length()
            //     .min(Elem::from(Concrete::from(U256::MAX)));
            // let range = SolcRange::new(len_min, len_max, vec![]);

            // let len_var = ContextVar {
            //     loc: Some(loc),
            //     name,
            //     display_name: array.display_name(self).into_expr_err(loc)? + ".length",
            //     storage: None,
            //     is_tmp: false,
            //     tmp_of: None,
            //     is_symbolic: true,
            //     is_return: false,
            //     ty: VarType::BuiltIn(
            //         BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
            //         Some(range),
            //     ),
            // };
            // let len_node = ContextVarNode::from(self.add_node(Node::ContextVar(len_var)));
            // self.add_edge(
            //     len_node,
            //     array,
            //     Edge::Context(ContextEdge::AttrAccess("length")),
            // );
            // self.add_edge(len_node, ctx, Edge::Context(ContextEdge::Variable));
            // ctx.add_var(len_node, self).into_expr_err(loc)?;

            // // we have to force here to avoid length <-> array recursion
            // let next_next_arr =
            //     self.advance_var_in_ctx_forcible(array.latest_version(self), loc, ctx, true)?;
            // let update_array_len =
            //     Elem::from(next_arr.latest_version(self)).set_length(len_node.into());

            // // Update the array
            // next_next_arr
            //     .set_range_min(self, update_array_len.clone())
            //     .into_expr_err(loc)?;
            // next_next_arr
            //     .set_range_max(self, update_array_len.clone())
            //     .into_expr_err(loc)?;

            // if !return_var {
            //     ctx.push_expr(ExprRet::Single(len_node.into()), self)
            //         .into_expr_err(loc)?;
            //     Ok(None)
            // } else {
            //     Ok(Some(len_node))
            // }
        }
    }

    fn create_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        loc: Loc,
        array: ContextVarNode,
        target_array: ContextVarNode,
        return_var: bool,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        // no length variable, create one
        let name = format!("{}.length", array.name(self).into_expr_err(loc)?);

        // Create the range from the current length or default to [0, uint256.max]
        let len_min = Elem::from(array)
            .get_length()
            .max(Elem::from(Concrete::from(U256::zero())));
        let len_max = Elem::from(array)
            .get_length()
            .min(Elem::from(Concrete::from(U256::MAX)));
        let range = SolcRange::new(len_min, len_max, vec![]);

        let len_var = ContextVar {
            loc: Some(loc),
            name,
            display_name: array.display_name(self).into_expr_err(loc)? + ".length",
            storage: None,
            is_tmp: false,
            tmp_of: None,
            dep_on: None,
            is_symbolic: true,
            is_return: false,
            ty: VarType::BuiltIn(
                BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                Some(range),
            ),
        };
        let len_node = ContextVarNode::from(self.add_node(Node::ContextVar(len_var)));
        self.add_edge(
            len_node,
            target_array,
            Edge::Context(ContextEdge::AttrAccess("length")),
        );
        self.add_edge(len_node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(len_node, self).into_expr_err(loc)?;

        // we have to force here to avoid length <-> array recursion
        let next_target_arr =
            self.advance_var_in_ctx_forcible(target_array.latest_version(self), loc, ctx, true)?;
        let update_array_len =
            Elem::from(target_array.latest_version(self)).set_length(len_node.into());

        // Update the array
        next_target_arr
            .set_range_min(self, arena, update_array_len.clone())
            .into_expr_err(loc)?;
        next_target_arr
            .set_range_max(self, arena, update_array_len.clone())
            .into_expr_err(loc)?;

        if !return_var {
            ctx.push_expr(ExprRet::Single(len_node.into()), self)
                .into_expr_err(loc)?;
            Ok(None)
        } else {
            Ok(Some(len_node))
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list and create it as a temporary variable
    fn tmp_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        arr: ContextVarNode,
        array_ctx: ContextNode,
        loc: Loc,
    ) -> ContextVarNode {
        let arr = arr.first_version(self);
        let name = format!("{}.length", arr.name(self).unwrap());
        tracing::trace!("Length access: {}", name);
        if let Some(attr_var) = array_ctx.var_by_name_or_recurse(self, &name).unwrap() {
            attr_var.latest_version(self)
        } else {
            let range = if let Ok(Some(size)) = arr.ty(self).unwrap().maybe_array_size(self) {
                SolcRange::from(Concrete::from(size))
            } else {
                SolcRange::try_from_builtin(&Builtin::Uint(256))
            };

            let len_var = ContextVar {
                loc: Some(loc),
                name: arr.name(self).unwrap() + ".length",
                display_name: arr.display_name(self).unwrap() + ".length",
                storage: None,
                is_tmp: false,
                tmp_of: None,
                dep_on: None,
                is_symbolic: true,
                is_return: false,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    range,
                ),
            };
            let len_node = self.add_node(Node::ContextVar(len_var));

            let next_arr = self
                .advance_var_in_ctx(arr.latest_version(self), loc, array_ctx)
                .unwrap();
            if next_arr
                .underlying(self)
                .unwrap()
                .ty
                .is_dyn_builtin(self)
                .unwrap()
            {
                if let Some(r) = next_arr.ref_range(self).unwrap() {
                    let min = r.simplified_range_min(self, arena).unwrap();
                    let max = r.simplified_range_max(self, arena).unwrap();
                    if let Some(mut rd) = min.maybe_range_dyn() {
                        ContextVarNode::from(len_node)
                            .set_range_min(self, arena, *rd.len.clone())
                            .unwrap();
                        rd.len = Box::new(Elem::from(len_node));
                        let res = next_arr
                            .set_range_min(self, arena, Elem::ConcreteDyn(rd))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        ContextVarNode::from(len_node)
                            .set_range_max(self, arena, *rd.len.clone())
                            .unwrap();
                        rd.len = Box::new(Elem::from(len_node));
                        let res = next_arr
                            .set_range_max(self, arena, Elem::ConcreteDyn(rd))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                }
            }

            self.add_edge(
                len_node,
                arr,
                Edge::Context(ContextEdge::AttrAccess("length")),
            );
            self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
            array_ctx.add_var(len_node.into(), self).unwrap();
            len_node.into()
        }
    }
}
