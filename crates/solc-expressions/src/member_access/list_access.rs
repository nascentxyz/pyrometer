use crate::Variable;

use graph::{
    elem::*,
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Range, SolcRange, VarType,
};
use shared::{ExprErr, IntoExprErr, RangeArena};

use alloy_primitives::U256;
use solang_parser::pt::{Expression, Loc};

impl<T> ListAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles list/array member access (indices, length, etc)
pub trait ListAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        input: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        self.match_length(arena, ctx, input, loc)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn match_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        elem_path: ExprRet,
        loc: Loc,
    ) -> Result<(), ExprErr> {
        match elem_path {
            ExprRet::Null => {
                ctx.push_expr(ExprRet::Null, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(arr) => {
                self.get_length(arena, ctx, arr.into(), false, loc)?;
                Ok(())
            }
            e => todo!("here: {e:?}"),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn get_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        array: ContextVarNode,
        return_var: bool,
        loc: Loc,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        let array = array.latest_version_or_inherited_in_ctx(ctx, self);
        // search for latest length
        if let Some(len_var) = array.array_to_len_var(self) {
            let len_node = self.advance_var_in_ctx(
                arena,
                len_var.latest_version_or_inherited_in_ctx(ctx, self),
                loc,
                ctx,
            )?;
            if !return_var {
                ctx.push_expr(ExprRet::Single(len_node.into()), self)
                    .into_expr_err(loc)?;
                Ok(None)
            } else {
                Ok(Some(len_node))
            }
        } else {
            self.create_length(arena, ctx, array, return_var, loc)
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn create_length(
        &mut self,
        arena: &mut RangeArena<Elem<Concrete>>,
        ctx: ContextNode,
        array: ContextVarNode,
        return_var: bool,
        loc: Loc,
    ) -> Result<Option<ContextVarNode>, ExprErr> {
        // no length variable, create one
        let name = format!("{}.length", array.name(self).into_expr_err(loc)?);

        let array = array.latest_version_or_inherited_in_ctx(ctx, self);
        // we have to force here to avoid length <-> array recursion
        let target_arr = self.advance_var_in_ctx_forcible(arena, array, loc, ctx, true)?;

        // Create the range from the current length or default to [0, uint256.max]
        let len_min = Elem::from(array)
            .get_length()
            .max(Elem::from(Concrete::from(U256::ZERO)));
        let len_max = Elem::from(array)
            .get_length()
            .min(Elem::from(Concrete::from(U256::MAX)));
        let range = SolcRange::new(len_min, len_max, vec![]);

        let len_var = ContextVar {
            loc: Some(loc),
            name,
            display_name: array.display_name(self).into_expr_err(loc)? + ".length",
            storage: *array.storage(self).into_expr_err(loc)?,
            is_tmp: false,
            tmp_of: None,
            dep_on: None,
            is_symbolic: true,
            is_return: false,
            is_fundamental: None,
            ty: VarType::BuiltIn(
                BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                Some(range),
            ),
        };
        let len_node = ContextVarNode::from(self.add_node(len_var));
        self.add_edge(
            len_node,
            target_arr,
            Edge::Context(ContextEdge::AttrAccess("length")),
        );
        self.add_edge(len_node, ctx, Edge::Context(ContextEdge::Variable));
        ctx.add_var(len_node, self).into_expr_err(loc)?;

        let update_array_len = Elem::from(target_arr.latest_version_or_inherited_in_ctx(ctx, self))
            .set_length(len_node.into());

        // Update the array
        target_arr
            .set_range_min(self, arena, update_array_len.clone())
            .into_expr_err(loc)?;
        target_arr
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
            attr_var.latest_version_or_inherited_in_ctx(array_ctx, self)
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
                storage: *arr.storage(self).unwrap(),
                is_tmp: false,
                tmp_of: None,
                dep_on: None,
                is_symbolic: true,
                is_return: false,
                is_fundamental: None,
                ty: VarType::BuiltIn(
                    BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                    range,
                ),
            };
            let len_node = self.add_node(len_var);

            let next_arr = self
                .advance_var_in_ctx(
                    arena,
                    arr.latest_version_or_inherited_in_ctx(array_ctx, self),
                    loc,
                    array_ctx,
                )
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
