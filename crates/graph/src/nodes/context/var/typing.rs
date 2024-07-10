use crate::{
    elem::Elem,
    nodes::{
        Builtin, Concrete, ContextNode, ContextVarNode, EnumNode, ErrorNode, StructNode, TyNode,
    },
    range::{
        elem::{RangeElem, RangeExpr, RangeOp},
        RangeEval,
    },
    AnalyzerBackend, ContextEdge, Edge, GraphBackend, GraphError, Node, TypeNode, VarType,
};

use shared::{GraphError, RangeArena, Search, StorageLocation};

use ethers_core::types::{I256, U256};
use petgraph::{visit::EdgeRef, Direction};
use solang_parser::pt::Loc;

impl ContextVarNode {
    pub fn ty<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a VarType, GraphError> {
        Ok(&self.underlying(analyzer)?.ty)
    }

    pub fn ty_max_concrete(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Concrete>, GraphError> {
        if let Ok(b) = self.underlying(analyzer)?.ty.as_builtin(analyzer) {
            if let Some(zero) = b.zero_concrete() {
                return Ok(Concrete::max_of_type(&zero));
            }
        }

        Ok(None)
    }
    pub fn ty_min_concrete(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Concrete>, GraphError> {
        if let Ok(b) = self.underlying(analyzer)?.ty.as_builtin(analyzer) {
            if let Some(zero) = b.zero_concrete() {
                return Ok(Concrete::min_of_type(&zero));
            }
        }

        Ok(None)
    }

    pub fn ty_zero_concrete(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Concrete>, GraphError> {
        if let Ok(b) = self.underlying(analyzer)?.ty.as_builtin(analyzer) {
            return Ok(b.zero_concrete());
        }

        Ok(None)
    }

    pub fn ty_eq_ty(
        &self,
        other: &VarType,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        self.ty(analyzer)?.ty_eq(other, analyzer)
    }

    pub fn is_mapping(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_mapping(analyzer)
    }

    pub fn is_dyn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_dyn(analyzer)
    }

    pub fn is_indexable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_indexable(analyzer)
    }

    pub fn is_storage(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Storage(..))
        ) || self.is_attr_or_index_of_storage(analyzer))
    }

    pub fn is_memory(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Memory(..))
        ))
    }

    pub fn maybe_struct(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<StructNode>, GraphError> {
        if let VarType::User(TypeNode::Struct(ut), _) = self.ty(analyzer)? {
            Ok(Some(*ut))
        } else {
            Ok(None)
        }
    }

    pub fn maybe_enum(&self, analyzer: &impl GraphBackend) -> Result<Option<EnumNode>, GraphError> {
        if let VarType::User(TypeNode::Enum(ut), _) = self.ty(analyzer)? {
            Ok(Some(*ut))
        } else {
            Ok(None)
        }
    }

    pub fn maybe_ty_node(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<TyNode>, GraphError> {
        if let VarType::User(TypeNode::Ty(ut), _) = self.ty(analyzer)? {
            Ok(Some(*ut))
        } else {
            Ok(None)
        }
    }

    pub fn maybe_err_node(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<ErrorNode>, GraphError> {
        if let VarType::User(TypeNode::Error(ut), _) = self.ty(analyzer)? {
            Ok(Some(*ut))
        } else {
            Ok(None)
        }
    }

    pub fn maybe_usertype(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<TypeNode>, GraphError> {
        if let VarType::User(ut, _) = self.ty(analyzer)? {
            Ok(Some(*ut))
        } else {
            Ok(None)
        }
    }

    pub fn is_return_assignment(&self, analyzer: &impl GraphBackend) -> bool {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .any(|edge| {
                Edge::Context(ContextEdge::ReturnAssign(true)) == *edge.weight()
                    || Edge::Context(ContextEdge::ReturnAssign(false)) == *edge.weight()
            })
    }

    pub fn is_ext_return_assignment(&self, analyzer: &impl GraphBackend) -> bool {
        analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Incoming)
            .any(|edge| Edge::Context(ContextEdge::ReturnAssign(true)) == *edge.weight())
    }

    pub fn is_storage_or_calldata_input(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        let global_first = self.global_first_version(analyzer);
        Ok(global_first.is_storage(analyzer)? || global_first.is_calldata_input(analyzer))
    }

    pub fn is_fundamental(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let global_first = self.global_first_version(analyzer);
        let is_independent = self.is_independent(analyzer)?;

        Ok(is_independent
            && (
                global_first.is_storage(analyzer)?
                    || global_first.is_calldata_input(analyzer)
                    || global_first.is_msg(analyzer)?
                    || global_first.is_block(analyzer)?
                    || (
                        // if its a function input, and we are evaluating the function
                        // as a standalone (i.e. its internal, but we are treating it like its external)
                        // it wont be marked as calldata, but for the purposes
                        // of determining controllability it is to better to assume there is some path that lets us
                        // control it
                        global_first.is_func_input(analyzer)
                            && global_first.maybe_ctx(analyzer).is_some()
                            && !global_first.ctx(analyzer).has_parent(analyzer)?
                    )
                    || self.is_attr_or_index_of_fundamental(analyzer)
                // performed last to try to not have to do this check
            ))
    }

    pub fn is_attr_or_index_of_fundamental(&self, analyzer: &impl GraphBackend) -> bool {
        let direct_is_fundamental = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .any(|edge| {
                if matches!(
                    edge.weight(),
                    Edge::Context(ContextEdge::AttrAccess(_))
                        | Edge::Context(ContextEdge::IndexAccess)
                        | Edge::Context(ContextEdge::Index)
                ) {
                    ContextVarNode::from(edge.target())
                        .is_fundamental(analyzer)
                        .unwrap_or(false)
                } else {
                    false
                }
            });
        if direct_is_fundamental {
            direct_is_fundamental
        } else if let Some(prev) = self.previous_global_version(analyzer) {
            prev.is_attr_or_index_of_fundamental(analyzer)
        } else {
            false
        }
    }

    pub fn is_attr_or_index_of_storage(&self, analyzer: &impl GraphBackend) -> bool {
        let direct_is_storage = analyzer
            .graph()
            .edges_directed(self.0.into(), Direction::Outgoing)
            .any(|edge| {
                if matches!(
                    edge.weight(),
                    Edge::Context(ContextEdge::AttrAccess(_))
                        | Edge::Context(ContextEdge::IndexAccess)
                        | Edge::Context(ContextEdge::Index)
                ) {
                    ContextVarNode::from(edge.target())
                        .is_storage(analyzer)
                        .unwrap_or(false)
                } else {
                    false
                }
            });
        if direct_is_storage {
            direct_is_storage
        } else if let Some(prev) = self.previous_or_inherited_version(analyzer) {
            prev.is_attr_or_index_of_storage(analyzer)
        } else {
            false
        }
    }

    pub fn is_independent(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.dependent_on(analyzer, false)?.is_empty() && self.tmp_of(analyzer)?.is_none())
    }

    pub fn is_controllable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self
            .dependent_on(analyzer, true)?
            .iter()
            .any(|dependent_on| {
                if let Ok(t) = dependent_on.is_fundamental(analyzer) {
                    t
                } else {
                    false
                }
            }))
    }

    pub fn is_calldata_input(&self, analyzer: &impl GraphBackend) -> bool {
        let global_first = self.global_first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(global_first.0.into(), Direction::Outgoing)
            .any(|edge| Edge::Context(ContextEdge::CalldataVariable) == *edge.weight())
    }

    pub fn is_msg(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Msg(..))
        ))
    }

    pub fn is_block(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.storage,
            Some(StorageLocation::Block(..))
        ))
    }

    pub fn is_func_input(&self, analyzer: &impl GraphBackend) -> bool {
        let first = self.first_version(analyzer);
        analyzer
            .graph()
            .edges_directed(first.0.into(), Direction::Outgoing)
            .any(|edge| {
                Edge::Context(ContextEdge::InputVariable) == *edge.weight()
                    || Edge::Context(ContextEdge::CalldataVariable) == *edge.weight()
            })
    }

    pub fn is_const(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        underlying.ty.is_const(analyzer, arena)
    }

    pub fn is_symbolic(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_symbolic)
    }

    pub fn is_tmp(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.is_tmp())
    }

    pub fn is_return_node(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        if let Some(ctx) = self.maybe_ctx(analyzer) {
            return Ok(ctx
                .underlying(analyzer)?
                .ret
                .iter()
                .any(|(_, node)| node.name(analyzer).unwrap() == self.name(analyzer).unwrap()));
        }
        Ok(false)
    }

    pub fn is_return_node_in_any(
        &self,
        ctxs: &[ContextNode],
        analyzer: &impl GraphBackend,
    ) -> bool {
        ctxs.iter().any(|ctx| {
            ctx.underlying(analyzer)
                .unwrap()
                .ret
                .iter()
                .any(|(_, node)| node.name(analyzer).unwrap() == self.name(analyzer).unwrap())
        })
    }

    pub fn is_len_var(&self, analyzer: &impl GraphBackend) -> bool {
        analyzer
            .search_for_ancestor(
                self.first_version(analyzer).into(),
                &Edge::Context(ContextEdge::AttrAccess("length")),
            )
            .is_some()
    }

    pub fn is_array_index_access(&self, analyzer: &impl GraphBackend) -> bool {
        analyzer
            .search_for_ancestor(
                self.first_version(analyzer).into(),
                &Edge::Context(ContextEdge::IndexAccess),
            )
            .is_some()
    }

    pub fn is_concrete(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(self.ty(analyzer)?, VarType::Concrete(_)))
    }

    pub fn as_concrete(&self, analyzer: &impl GraphBackend) -> Result<Concrete, GraphError> {
        match &self.ty(analyzer)? {
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.clone()),
            e => Err(GraphError::NodeConfusion(format!(
                "Expected variable type to be concrete but was: {e:?}"
            ))),
        }
    }

    pub fn as_cast_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        cast_ty: Builtin,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Self, GraphError> {
        let new_underlying = self
            .underlying(analyzer)?
            .clone()
            .as_cast_tmp(loc, ctx, cast_ty, analyzer)?;
        let node = analyzer.add_node(Node::ContextVar(new_underlying));
        ctx.add_var(node.into(), analyzer)?;
        analyzer.add_edge(node, ctx, Edge::Context(ContextEdge::Variable));
        Ok(node.into())
    }

    pub fn as_tmp(
        &self,
        loc: Loc,
        ctx: ContextNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Self, GraphError> {
        let new_underlying = self
            .underlying(analyzer)?
            .clone()
            .as_tmp(loc, ctx, analyzer)?;
        Ok(analyzer.add_node(Node::ContextVar(new_underlying)).into())
    }

    pub fn ty_eq(
        &self,
        other: &Self,
        analyzer: &mut impl GraphBackend,
    ) -> Result<bool, GraphError> {
        self.ty(analyzer)?.ty_eq(other.ty(analyzer)?, analyzer)
    }

    /// Performs an in-place cast
    pub fn cast_from(
        &self,
        other: &Self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let other_ty = other.ty(analyzer)?.clone();
        if other_ty.ty_eq(&self.underlying(analyzer)?.ty, analyzer)? {
            return Ok(());
        }

        let min_expr = Elem::Expr(RangeExpr::new(
            self.range_min(analyzer)?.expect("Should have a minimum"),
            RangeOp::Cast,
            Elem::from(*other),
        ));

        let max_expr = Elem::Expr(RangeExpr::new(
            self.range_max(analyzer)?.expect("Should have a maximum"),
            RangeOp::Cast,
            Elem::from(*other),
        ));

        self.underlying_mut(analyzer)?.ty = other_ty;

        self.set_range_min(analyzer, arena, min_expr)?;
        self.set_range_max(analyzer, arena, max_expr)?;
        Ok(())
    }

    pub fn literal_cast_from(
        &self,
        other: &Self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let to_ty = other.ty(analyzer)?.clone();
        self.literal_cast_from_ty(to_ty, analyzer)?;
        Ok(())
    }

    // pub fn cast_from_ty(
    //     &self,
    //     to_ty: VarType,
    //     analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    // ) -> Result<(), GraphError> {
    //     let new_underlying = self.underlying(analyzer)?.clone();
    //     let node = analyzer.add_node(Node::ContextVar(new_underlying));
    //     analyzer.add_edge(node, *self, Edge::Context(ContextEdge::Prev));
    //     let new_self = ContextVarNode::from(node);

    //     let from_ty = self.ty(analyzer)?.clone();
    //     if !from_ty.ty_eq(&to_ty, analyzer)? {
    //         if let Some(new_ty) = from_ty.try_cast(&to_ty, analyzer)? {
    //             new_self.underlying_mut(analyzer)?.ty = new_ty;
    //         }

    //         if let Some((new_min, new_max)) = self.cast_exprs(&to_ty, analyzer)? {
    //             new_self.set_range_min(analyzer, new_min)?;
    //             new_self.set_range_max(analyzer, new_max)?;
    //         }
    //     }

    //     if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (new_self.ty(analyzer)?, to_ty) {
    //         // update name
    //         let display_name = cnode.underlying(analyzer)?.as_human_string();
    //         new_self.underlying_mut(analyzer)?.display_name = display_name;
    //     }
    //     Ok(())
    // }

    pub fn cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let from_ty = self.ty(analyzer)?.clone();
        if !from_ty.ty_eq(&to_ty, analyzer)? {
            if let Some(new_ty) = from_ty.clone().try_cast(&to_ty, analyzer)? {
                self.underlying_mut(analyzer)?.ty = new_ty;
            }

            if let (Some(mut r), Some(r2)) =
                (self.ty_mut(analyzer)?.take_range(), to_ty.range(analyzer)?)
            {
                r.min.arenaize(analyzer, arena)?;
                r.max.arenaize(analyzer, arena)?;

                let mut min_expr = r
                    .min
                    .clone()
                    .cast(r2.min.clone())
                    .min(r.max.clone().cast(r2.min.clone()));
                let mut max_expr = r
                    .min
                    .clone()
                    .cast(r2.min.clone())
                    .max(r.max.clone().cast(r2.min));

                min_expr.arenaize(analyzer, arena)?;
                max_expr.arenaize(analyzer, arena)?;

                let zero = Elem::from(Concrete::from(U256::zero()));
                if r.contains_elem(&zero, analyzer, arena) {
                    min_expr = min_expr.min(zero.clone());
                    max_expr = max_expr.max(zero);
                }

                if let (VarType::BuiltIn(from_bn, _), VarType::BuiltIn(to_bn, _)) =
                    (self.ty(analyzer)?, to_ty.clone())
                {
                    match (from_bn.underlying(analyzer)?, to_bn.underlying(analyzer)?) {
                        (Builtin::Uint(_), int @ Builtin::Int(_)) => {
                            // from ty is uint, to ty is int, check if type(int<SIZE>.min).bit_representation()
                            // is in range
                            if let Some(r) = self.ref_range(analyzer)? {
                                let int_min = int.min_concrete().unwrap();
                                let bit_repr = int_min.bit_representation().unwrap();
                                let bit_repr = bit_repr.into();
                                if r.contains_elem(&bit_repr, analyzer, arena) {
                                    min_expr = min_expr.min(int_min.clone().into());
                                    max_expr = max_expr.max(int_min.into());
                                }
                            }
                        }
                        (Builtin::Int(_), Builtin::Uint(_size)) => {
                            // from ty is int, to ty is uint
                            if let Some(r) = self.ref_range(analyzer)? {
                                let neg1 = Concrete::from(I256::from(-1i32));
                                if r.contains_elem(&neg1.clone().into(), analyzer, arena) {
                                    max_expr =
                                        max_expr.max(neg1.bit_representation().unwrap().into());
                                }
                            }
                        }
                        _ => {}
                    }
                }
                r.min = min_expr;
                r.max = max_expr;
                r.min.arenaize(analyzer, arena)?;
                r.max.arenaize(analyzer, arena)?;
                self.set_range(analyzer, r)?;
            }
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_string();
            self.underlying_mut(analyzer)?.display_name = display_name;
        }
        Ok(())
    }

    pub fn literal_cast_from_ty(
        &self,
        to_ty: VarType,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        let from_ty = self.ty(analyzer)?.clone();
        if !from_ty.ty_eq(&to_ty, analyzer)? {
            if let Some(new_ty) = from_ty.try_literal_cast(&to_ty, analyzer)? {
                self.underlying_mut(analyzer)?.ty = new_ty;
            }
            // we dont need to update the ranges because a literal by definition is concrete
        }

        if let (VarType::Concrete(_), VarType::Concrete(cnode)) = (self.ty(analyzer)?, to_ty) {
            // update name
            let display_name = cnode.underlying(analyzer)?.as_human_string();
            self.underlying_mut(analyzer)?.display_name = display_name;
        }
        Ok(())
    }

    pub fn try_increase_size(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let from_ty = self.ty(analyzer)?.clone();
        self.cast_from_ty(from_ty.max_size(analyzer)?, analyzer, arena)?;
        Ok(())
    }

    pub fn is_int(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        self.ty(analyzer)?.is_int(analyzer)
    }

    pub fn cast_exprs(
        &self,
        to_ty: &VarType,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<(Elem<Concrete>, Elem<Concrete>)>, GraphError> {
        if let Some(to_range) = to_ty.range(analyzer)? {
            let mut min_expr = (*self)
                .range_min(analyzer)?
                .expect(&format!(
                    "{:?}, {} had no min",
                    self.loc(analyzer).unwrap(),
                    self.display_name(analyzer).unwrap()
                ))
                .cast(to_range.min.clone())
                .min(
                    (*self)
                        .range_max(analyzer)?
                        .unwrap()
                        .cast(to_range.min.clone()),
                );
            let mut max_expr = (*self)
                .range_min(analyzer)?
                .unwrap()
                .cast(to_range.min.clone())
                .max((*self).range_max(analyzer)?.unwrap().cast(to_range.min));

            if let Some(r) = self.ref_range(analyzer)? {
                let zero = Elem::from(Concrete::from(U256::zero()));
                if r.contains_elem(&zero, analyzer, arena) {
                    min_expr = min_expr.min(zero.clone());
                    max_expr = max_expr.max(zero);
                }
            }

            if let (VarType::BuiltIn(from_bn, _), VarType::BuiltIn(to_bn, _)) =
                (self.ty(analyzer)?, to_ty)
            {
                match (from_bn.underlying(analyzer)?, to_bn.underlying(analyzer)?) {
                    (Builtin::Uint(_), int @ Builtin::Int(_)) => {
                        // from ty is uint, to ty is int, check if type(int<SIZE>.min).bit_representation()
                        // is in range
                        if let Some(r) = self.ref_range(analyzer)? {
                            let int_min = int.min_concrete().unwrap();
                            let bit_repr = int_min.bit_representation().unwrap();
                            let bit_repr = bit_repr.into();
                            if r.contains_elem(&bit_repr, analyzer, arena) {
                                min_expr = min_expr.min(int_min.clone().into());
                                max_expr = max_expr.max(int_min.into());
                            }
                        }
                    }
                    (Builtin::Int(_), Builtin::Uint(_size)) => {
                        // from ty is int, to ty is uint
                        if let Some(r) = self.ref_range(analyzer)? {
                            let neg1 = Concrete::from(I256::from(-1i32));
                            if r.contains_elem(&neg1.clone().into(), analyzer, arena) {
                                max_expr = max_expr.max(neg1.bit_representation().unwrap().into());
                            }
                        }
                    }
                    _ => {}
                }
            }

            Ok(Some((min_expr, max_expr)))
        } else {
            Ok(None)
        }
    }
}
