use crate::{ContextBuilder, ExprErr, IntoExprErr, Variable, ExpressionParser};

use graph::{
    elem::*,
    nodes::{BuiltInNode, Builtin, Concrete, ContextNode, ContextVar, ContextVarNode, ExprRet},
    AnalyzerBackend, ContextEdge, Edge, Node, Range, SolcRange, VarType,
};
use shared::NodeIdx;

use solang_parser::pt::{Expression, Identifier, Loc};

impl<T> ListAccess for T where T: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {}
/// Handles list/array member access (indices, length, etc)
pub trait ListAccess: AnalyzerBackend<Expr = Expression, ExprErr = ExprErr> + Sized {
    #[tracing::instrument(level = "trace", skip_all)]
    /// Access an index of a list/array
    fn index_access(
        &mut self,
        loc: Loc,
        parent: NodeIdx,
        dyn_builtin: BuiltInNode,
        ident: &Identifier,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.variable(ident, ctx, None)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
            let Some(index_paths) = ctx.pop_expr_latest(loc, analyzer).into_expr_err(loc)? else {
                return Err(ExprErr::NoRhs(loc, "No index in index access".to_string()));
            };

            if matches!(index_paths, ExprRet::CtxKilled(_)) {
                ctx.push_expr(index_paths, analyzer).into_expr_err(loc)?;
                return Ok(());
            }
            analyzer.match_index_access(&index_paths, loc, parent.into(), dyn_builtin, ctx)
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Match on the [`ExprRet`] of a index access expression
    fn match_index_access(
        &mut self,
        index_paths: &ExprRet,
        loc: Loc,
        parent: ContextVarNode,
        dyn_builtin: BuiltInNode,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        match index_paths {
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, *kind).into_expr_err(loc),
            ExprRet::Single(idx) => {
                let parent = parent.first_version(self);
                let parent_name = parent.name(self).into_expr_err(loc)?;
                let parent_display_name = parent.display_name(self).unwrap();

                tracing::trace!(
                    "Index access: {}[{}]",
                    parent_display_name,
                    ContextVarNode::from(*idx)
                        .display_name(self)
                        .into_expr_err(loc)?
                );
                let parent_ty = dyn_builtin;
                let parent_stor = parent
                    .storage(self)
                    .into_expr_err(loc)?
                    .as_ref()
                    .expect("parent didnt have a storage location?");
                let indexed_var = ContextVar::new_from_index(
                    self,
                    loc,
                    parent_name,
                    parent_display_name,
                    *parent_stor,
                    &parent_ty,
                    ContextVarNode::from(*idx),
                )
                .into_expr_err(loc)?;

                let idx_node = self.add_node(Node::ContextVar(indexed_var));
                self.add_edge(idx_node, parent, Edge::Context(ContextEdge::IndexAccess));
                self.add_edge(idx_node, ctx, Edge::Context(ContextEdge::Variable));
                ctx.add_var(idx_node.into(), self).into_expr_err(loc)?;
                self.add_edge(*idx, idx_node, Edge::Context(ContextEdge::Index));
                ctx.push_expr(ExprRet::Single(idx_node), self)
                    .into_expr_err(loc)?;
                Ok(())
            }
            e => Err(ExprErr::UnhandledExprRet(
                loc,
                format!("Unhandled expression return in index access: {e:?}"),
            )),
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn length(
        &mut self,
        loc: Loc,
        input_expr: &Expression,
        ctx: ContextNode,
    ) -> Result<(), ExprErr> {
        self.parse_ctx_expr(input_expr, ctx)?;
        self.apply_to_edges(ctx, loc, &|analyzer, ctx, loc| {
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
            analyzer.match_length(ctx, loc, ret, true)
        })
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list and create it as a temporary variable
    fn tmp_length(
        &mut self,
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
                    let min = r.evaled_range_min(self).unwrap();
                    let max = r.evaled_range_max(self).unwrap();

                    if let Some(mut rd) = min.maybe_range_dyn() {
                        rd.len = Elem::from(len_node);
                        let res = next_arr
                            .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }

                    if let Some(mut rd) = max.maybe_range_dyn() {
                        rd.len = Elem::from(len_node);
                        let res = next_arr
                            .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                            .into_expr_err(loc);
                        let _ = self.add_if_err(res);
                    }
                }
            }

            self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
            self.add_edge(len_node, array_ctx, Edge::Context(ContextEdge::Variable));
            array_ctx.add_var(len_node.into(), self).unwrap();
            len_node.into()
        }
    }

    #[tracing::instrument(level = "trace", skip_all)]
    /// Get the length member of an array/list
    fn match_length(
        &mut self,
        ctx: ContextNode,
        loc: Loc,
        elem_path: ExprRet,
        update_len_bound: bool,
    ) -> Result<(), ExprErr> {
        match elem_path {
            ExprRet::Null => {
                ctx.push_expr(ExprRet::Null, self).into_expr_err(loc)?;
                Ok(())
            }
            ExprRet::CtxKilled(kind) => ctx.kill(self, loc, kind).into_expr_err(loc),
            ExprRet::Single(arr) => {
                let next_arr = self.advance_var_in_ctx(
                    ContextVarNode::from(arr).latest_version(self),
                    loc,
                    ctx,
                )?;
                let arr = ContextVarNode::from(arr).first_version(self);
                let name = format!("{}.length", arr.name(self).into_expr_err(loc)?);
                tracing::trace!("Length access: {}", name);
                if let Some(len_var) = ctx.var_by_name_or_recurse(self, &name).into_expr_err(loc)? {
                    let len_var = len_var.latest_version(self);
                    let new_len = self.advance_var_in_ctx(len_var, loc, ctx)?;
                    if update_len_bound
                        && next_arr
                            .underlying(self)
                            .into_expr_err(loc)?
                            .ty
                            .is_dyn_builtin(self)
                            .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::from(new_len);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::from(new_len);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }
                    ctx.push_expr(ExprRet::Single(new_len.into()), self)
                        .into_expr_err(loc)?;
                    Ok(())
                } else {
                    let range = if let Ok(Some(size)) =
                        arr.ty(self).into_expr_err(loc)?.maybe_array_size(self)
                    {
                        SolcRange::from(Concrete::from(size))
                    } else {
                        SolcRange::try_from_builtin(&Builtin::Uint(256))
                    };

                    let len_var = ContextVar {
                        loc: Some(loc),
                        name,
                        display_name: arr.display_name(self).into_expr_err(loc)? + ".length",
                        storage: None,
                        is_tmp: false,
                        tmp_of: None,
                        is_symbolic: true,
                        is_return: false,
                        ty: VarType::BuiltIn(
                            BuiltInNode::from(self.builtin_or_add(Builtin::Uint(256))),
                            range,
                        ),
                    };
                    let len_node = self.add_node(Node::ContextVar(len_var));

                    if next_arr
                        .underlying(self)
                        .into_expr_err(loc)?
                        .ty
                        .is_dyn_builtin(self)
                        .into_expr_err(loc)?
                    {
                        if let Some(r) = next_arr.ref_range(self).into_expr_err(loc)? {
                            let min = r.evaled_range_min(self).into_expr_err(loc)?;
                            let max = r.evaled_range_max(self).into_expr_err(loc)?;

                            if let Some(mut rd) = min.maybe_range_dyn() {
                                rd.len = Elem::from(len_node);
                                let res = next_arr
                                    .set_range_min(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }

                            if let Some(mut rd) = max.maybe_range_dyn() {
                                rd.len = Elem::from(len_node);
                                let res = next_arr
                                    .set_range_max(self, Elem::ConcreteDyn(Box::new(rd)))
                                    .into_expr_err(loc);
                                let _ = self.add_if_err(res);
                            }
                        }
                    }

                    self.add_edge(len_node, arr, Edge::Context(ContextEdge::AttrAccess));
                    self.add_edge(len_node, ctx, Edge::Context(ContextEdge::Variable));
                    ctx.add_var(len_node.into(), self).into_expr_err(loc)?;
                    ctx.push_expr(ExprRet::Single(len_node), self)
                        .into_expr_err(loc)?;
                    Ok(())
                }
            }
            e => todo!("here: {e:?}"),
        }
    }
}
