use crate::{
    nodes::{
        BuiltInNode, Builtin, Concrete, ConcreteNode, ContractNode, EnumNode, ErrorNode,
        FunctionNode, StructNode, TyNode,
    },
    range::{
        elem::{Elem, RangeElem},
        Range, SolcRange,
    },
    AnalyzerBackend, AsDotStr, GraphBackend, Node,
};
use shared::{GraphError, RangeArena};

use shared::NodeIdx;

use alloy_primitives::{Address, U256};

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum VarType {
    User(TypeNode, Option<SolcRange>),
    BuiltIn(BuiltInNode, Option<SolcRange>),
    Concrete(ConcreteNode),
}

impl AsDotStr for VarType {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        self.as_string(analyzer).unwrap()
    }
}

impl VarType {
    pub fn rangeless_clone(&self) -> Self {
        match self {
            VarType::User(t, _) => VarType::User(*t, None),
            VarType::BuiltIn(t, _) => VarType::BuiltIn(*t, None),
            VarType::Concrete(t) => VarType::Concrete(*t),
        }
    }

    pub fn set_range(&mut self, new_range: SolcRange) -> Result<(), GraphError> {
        match self {
            VarType::User(TypeNode::Enum(_), ref mut r)
            | VarType::User(TypeNode::Contract(_), ref mut r)
            | VarType::User(TypeNode::Ty(_), ref mut r)
            | VarType::BuiltIn(_, ref mut r) => {
                *r = Some(new_range);
                Ok(())
            }
            _ => Err(GraphError::NodeConfusion(
                "This type cannot have a range".to_string(),
            )),
        }
    }

    pub fn take_range(&mut self) -> Option<SolcRange> {
        match self {
            VarType::User(TypeNode::Enum(_), ref mut r)
            | VarType::User(TypeNode::Contract(_), ref mut r)
            | VarType::User(TypeNode::Ty(_), ref mut r)
            | VarType::BuiltIn(_, ref mut r) => r.take(),
            _ => None,
        }
    }

    pub fn possible_builtins_from_ty_inf(&self, analyzer: &impl GraphBackend) -> Vec<Builtin> {
        match self {
            Self::BuiltIn(bn, _) => bn
                .underlying(analyzer)
                .unwrap()
                .possible_builtins_from_ty_inf(),
            Self::Concrete(c) => c
                .underlying(analyzer)
                .unwrap()
                .possible_builtins_from_ty_inf(),
            _ => vec![],
        }
    }

    pub fn ty_idx(&self) -> NodeIdx {
        match self {
            Self::User(ty_node, _) => (*ty_node).into(),
            Self::BuiltIn(bn, _) => (*bn).into(),
            Self::Concrete(c) => (*c).into(),
        }
    }

    pub fn empty_ty(&self) -> VarType {
        match self {
            Self::User(ty_node, _) => Self::User(*ty_node, None),
            Self::BuiltIn(bn, _) => Self::BuiltIn(*bn, None),
            Self::Concrete(c) => Self::Concrete(*c),
        }
    }

    pub fn is_dyn_builtin(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.is_dyn(analyzer),
            _ => Ok(false),
        }
    }

    pub fn is_string(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.is_string(analyzer),
            _ => Ok(false),
        }
    }

    pub fn is_bytes(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.is_bytes(analyzer),
            _ => Ok(false),
        }
    }

    pub fn unresolved_as_resolved(&self, analyzer: &impl GraphBackend) -> Result<Self, GraphError> {
        match self {
            VarType::User(TypeNode::Unresolved(n), _) => match analyzer.node(*n) {
                Node::Unresolved(ident) => Err(GraphError::NodeConfusion(format!(
                    "Expected the type \"{}\" to be resolved by now",
                    ident.name
                ))),
                _ => {
                    if let Some(ty) = VarType::try_from_idx(analyzer, *n) {
                        Ok(ty)
                    } else {
                        Err(GraphError::NodeConfusion(
                            "Tried to type a non-typeable element".to_string(),
                        ))
                    }
                }
            },
            _ => Ok(self.clone()),
        }
    }

    pub fn resolve_unresolved(&mut self, analyzer: &impl GraphBackend) -> Result<(), GraphError> {
        match self {
            VarType::User(TypeNode::Unresolved(n), _) => match analyzer.node(*n) {
                Node::Unresolved(ident) => Err(GraphError::NodeConfusion(format!(
                    "Expected the type \"{}\" to be resolved by now",
                    ident.name
                ))),
                _ => {
                    if let Some(ty) = VarType::try_from_idx(analyzer, *n) {
                        *self = ty;
                        Ok(())
                    } else {
                        Err(GraphError::NodeConfusion(
                            "Tried to type a non-typeable element".to_string(),
                        ))
                    }
                }
            },
            _ => Ok(()),
        }
    }

    pub fn concrete_to_builtin(
        &mut self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<(), GraphError> {
        if let VarType::Concrete(cnode) = self {
            let c = cnode.underlying(analyzer)?.clone();
            match c {
                Concrete::Uint(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Uint(*size))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::Int(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Int(*size))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::Bool(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bool)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::Address(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Address)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::Bytes(ref s, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bytes(*s))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::String(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::String)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                Concrete::DynBytes(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::DynamicBytes)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                // Concrete::Array(Vec<Concrete>),
                _ => {}
            }
        }
        Ok(())
    }

    pub fn try_from_idx(analyzer: &impl GraphBackend, node: NodeIdx) -> Option<VarType> {
        // get node, check if typeable and convert idx into vartype
        match analyzer.node(node) {
            Node::VarType(a) => Some(a.clone()),
            Node::Builtin(b) => Some(VarType::BuiltIn(
                node.into(),
                SolcRange::try_from_builtin(b),
            )),
            Node::Contract(_) => Some(VarType::User(
                TypeNode::Contract(node.into()),
                SolcRange::try_from_builtin(&Builtin::Address),
            )),
            Node::Function(_) => Some(VarType::User(TypeNode::Func(node.into()), None)),
            Node::Struct(_) => Some(VarType::User(TypeNode::Struct(node.into()), None)),
            Node::Error(_) => Some(VarType::User(TypeNode::Error(node.into()), None)),
            Node::Enum(enu) => {
                let variants = enu.variants();
                let range = if !variants.is_empty() {
                    let min = Concrete::from(U256::ZERO).into();
                    let max = Concrete::from(U256::from(variants.len() - 1)).into();
                    Some(SolcRange::new(min, max, vec![]))
                } else {
                    None
                };
                Some(VarType::User(TypeNode::Enum(node.into()), range))
            }
            Node::Unresolved(_n) => Some(VarType::User(TypeNode::Unresolved(node), None)),
            Node::Concrete(_) => Some(VarType::Concrete(node.into())),
            Node::ContextVar(cvar) => Some(cvar.ty.clone()),
            Node::Var(var) => VarType::try_from_idx(analyzer, var.ty),
            Node::Ty(ty) => {
                let range = SolcRange::try_from_builtin(
                    BuiltInNode::from(ty.ty).underlying(analyzer).unwrap(),
                )?;
                Some(VarType::User(TypeNode::Ty(node.into()), Some(range)))
            }
            Node::FunctionParam(inner) => VarType::try_from_idx(analyzer, inner.ty),
            Node::ContextFork
            | Node::FunctionCall
            | Node::FunctionReturn(..)
            | Node::ErrorParam(..)
            | Node::Field(..)
            | Node::SourceUnitPart(..)
            | Node::SourceUnit(..)
            | Node::Entry
            | Node::Context(..)
            | Node::Msg(_)
            | Node::EnvCtx(_)
            | Node::Block(_)
            | Node::YulFunction(..) => None,
        }
    }

    pub fn requires_input(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.requires_input()),
            _ => Ok(false),
        }
    }

    pub fn implicitly_castable_to(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
        from_lit: bool,
    ) -> Result<bool, GraphError> {
        if self.ty_idx() == other.ty_idx() {
            return Ok(true);
        }

        let res = match (self, other) {
            (Self::BuiltIn(from_bn, _), Self::BuiltIn(to_bn, _)) => {
                from_bn.implicitly_castable_to(to_bn, analyzer)
            }
            (Self::Concrete(from), Self::BuiltIn(to, _)) => {
                let from = from.underlying(analyzer)?.as_builtin();
                let to = to.underlying(analyzer)?;
                Ok(from.implicitly_castable_to(to))
            }
            (Self::BuiltIn(from, _), Self::Concrete(to)) => {
                let from = from.underlying(analyzer)?;
                let to = to.underlying(analyzer)?.as_builtin();
                Ok(from.implicitly_castable_to(&to))
            }
            (Self::Concrete(from), Self::Concrete(to)) => {
                let from = from.underlying(analyzer)?.as_builtin();
                let to = to.underlying(analyzer)?.as_builtin();
                Ok(from.implicitly_castable_to(&to))
            }
            _ => Ok(false),
        };

        let impl_cast = res?;
        if !impl_cast && from_lit {
            match (self, other) {
                (Self::Concrete(from), Self::BuiltIn(to, _)) => {
                    let froms = from.underlying(analyzer)?.alt_lit_builtins();
                    let to = to.underlying(analyzer)?;

                    // exact matches only (i.e. uint160 -> address, uint8 -> bytes1, etc)
                    Ok(froms.iter().any(|from| from == to))
                }
                _ => Ok(impl_cast),
            }
        } else {
            Ok(impl_cast)
        }
    }

    pub fn try_cast(
        self,
        other: &Self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Option<Self>, GraphError> {
        match (self, other) {
            (l, Self::User(TypeNode::Ty(ty), o_r)) => {
                let t = Self::BuiltIn(BuiltInNode::from(ty.underlying(analyzer)?.ty), o_r.clone());
                l.try_cast(&t, analyzer)
            }
            (Self::BuiltIn(from_bn, sr), Self::User(TypeNode::Contract(cn), _)) => {
                match from_bn.underlying(analyzer)? {
                    Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                        Ok(Some(Self::User(TypeNode::Contract(*cn), sr)))
                    }
                    _ => Ok(None),
                }
            }
            (Self::User(TypeNode::Contract(_cn), sr), Self::BuiltIn(to_bn, _)) => {
                match to_bn.underlying(analyzer)? {
                    Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                        Ok(Some(Self::BuiltIn(*to_bn, sr)))
                    }
                    _ => Ok(None),
                }
            }
            (Self::BuiltIn(from_bn, sr), Self::BuiltIn(to_bn, _)) => {
                if from_bn.castable_to(to_bn, analyzer)? {
                    Ok(Some(Self::BuiltIn(*to_bn, sr)))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::BuiltIn(to_bn, _)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let b = to_bn.underlying(analyzer)?;
                if let Some(casted) = c.cast(b.clone()) {
                    let node = analyzer.add_node(casted);
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::Concrete(to_c)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let to_c = to_c.underlying(analyzer)?;
                if let Some(casted) = c.cast_from(to_c) {
                    let node = analyzer.add_node(casted);
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn builtin_to_concrete_idx(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<NodeIdx>, GraphError> {
        match self {
            Self::BuiltIn(bn, Some(range)) => {
                let Some(min) = range.evaled_range_min(analyzer, arena)?.maybe_concrete() else {
                    return Ok(None);
                };
                let Some(max) = range.evaled_range_max(analyzer, arena)?.maybe_concrete() else {
                    return Ok(None);
                };
                if min.val == max.val {
                    let builtin = bn.underlying(analyzer)?;
                    let Some(conc) = min.val.cast(builtin.clone()) else {
                        return Ok(None);
                    };
                    let conc_idx = analyzer.add_node(conc);
                    Ok(Some(conc_idx))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn try_literal_cast(
        self,
        other: &Self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<Option<Self>, GraphError> {
        match (self, other) {
            (Self::BuiltIn(from_bn, sr), Self::User(TypeNode::Ty(ty), _)) => {
                if ty.underlying(analyzer)?.ty == from_bn.into() {
                    Ok(Some(Self::User(TypeNode::Ty(*ty), sr)))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::User(TypeNode::Ty(ty), _)) => {
                let concrete_underlying = from_c.underlying(analyzer)?.clone();
                let as_bn = analyzer.builtin_or_add(concrete_underlying.as_builtin());
                if ty.underlying(analyzer)?.ty == as_bn {
                    Ok(Some(Self::User(
                        TypeNode::Ty(*ty),
                        SolcRange::from(concrete_underlying),
                    )))
                } else {
                    Ok(None)
                }
            }
            (Self::BuiltIn(from_bn, sr), Self::BuiltIn(to_bn, _)) => {
                if from_bn.castable_to(to_bn, analyzer)? {
                    Ok(Some(Self::BuiltIn(*to_bn, sr)))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::BuiltIn(to_bn, _)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let b = to_bn.underlying(analyzer)?;
                if let Some(casted) = c.literal_cast(b.clone()) {
                    let node = analyzer.add_node(casted);
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::Concrete(to_c)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let to_c = to_c.underlying(analyzer)?;
                if let Some(casted) = c.literal_cast_from(to_c) {
                    let node = analyzer.add_node(casted);
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn castable_to(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        match (self, other) {
            (Self::BuiltIn(from_bn, _), Self::BuiltIn(to_bn, _)) => {
                from_bn.castable_to(to_bn, analyzer)
            }
            (Self::Concrete(from_c), Self::BuiltIn(to_bn, _)) => {
                let to = to_bn.underlying(analyzer)?;
                Ok(from_c.underlying(analyzer)?.as_builtin().castable_to(to))
            }
            _ => Ok(false),
        }
    }

    pub fn max_size(&self, analyzer: &mut impl AnalyzerBackend) -> Result<Self, GraphError> {
        match self {
            Self::BuiltIn(from_bn, _r) => {
                let bn = from_bn.max_size(analyzer)?;
                Ok(Self::BuiltIn(
                    bn,
                    SolcRange::try_from_builtin(bn.underlying(analyzer)?),
                ))
            }
            Self::Concrete(from_c) => Ok(Self::Concrete(from_c.max_size(analyzer)?)),
            _ => Ok(self.clone()),
        }
    }

    pub fn range(&self, analyzer: &impl GraphBackend) -> Result<Option<SolcRange>, GraphError> {
        match self {
            Self::User(_, Some(range)) => Ok(Some(range.clone())),
            Self::BuiltIn(_, Some(range)) => Ok(Some(range.clone())),
            Self::BuiltIn(bn, None) => Ok(SolcRange::try_from_builtin(bn.underlying(analyzer)?)),
            Self::Concrete(cnode) => Ok(SolcRange::from(cnode.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn ref_range(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<std::borrow::Cow<'_, SolcRange>>, GraphError> {
        match self {
            Self::User(_, Some(range)) => Ok(Some(std::borrow::Cow::Borrowed(range))),
            Self::BuiltIn(_, Some(range)) => Ok(Some(std::borrow::Cow::Borrowed(range))),
            Self::BuiltIn(bn, None) => {
                if let Some(r) = SolcRange::try_from_builtin(bn.underlying(analyzer)?) {
                    Ok(Some(std::borrow::Cow::Owned(r)))
                } else {
                    Ok(None)
                }
            }
            Self::Concrete(cnode) => {
                if let Some(r) = SolcRange::from(cnode.underlying(analyzer)?.clone()) {
                    Ok(Some(std::borrow::Cow::Owned(r)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn delete_range_result(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<SolcRange>, GraphError> {
        match self {
            Self::User(TypeNode::Contract(_), _) => {
                let zero = Concrete::Address(Address::from_slice(&[0x00; 20]));
                Ok(Some(SolcRange::new(
                    zero.clone().into(),
                    zero.into(),
                    vec![],
                )))
            }
            Self::User(TypeNode::Enum(enum_node), _) => {
                if let Some(first) = enum_node.variants(analyzer)?.first() {
                    let zero = Concrete::from(first.clone());
                    Ok(Some(SolcRange::new(
                        zero.clone().into(),
                        zero.into(),
                        vec![],
                    )))
                } else {
                    Ok(None)
                }
            }
            Self::User(TypeNode::Ty(ty), _) => {
                BuiltInNode::from(ty.underlying(analyzer)?.ty).zero_range(analyzer)
            }
            Self::BuiltIn(bn, None) => bn.zero_range(analyzer),
            Self::Concrete(cnode) => Ok(cnode.underlying(analyzer)?.as_builtin().zero_range()),
            _ => Ok(None),
        }
    }

    pub fn default_range(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<SolcRange>, GraphError> {
        match self {
            Self::User(TypeNode::Contract(_), _) => {
                Ok(SolcRange::try_from_builtin(&Builtin::Address))
            }
            Self::User(TypeNode::Enum(enu), _) => enu.maybe_default_range(analyzer),
            Self::User(TypeNode::Ty(ty), _) => Ok(SolcRange::try_from_builtin(
                BuiltInNode::from(ty.underlying(analyzer)?.ty).underlying(analyzer)?,
            )),
            Self::BuiltIn(bn, _) => Ok(SolcRange::try_from_builtin(bn.underlying(analyzer)?)),
            Self::Concrete(cnode) => Ok(SolcRange::from(cnode.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn is_const(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        match self {
            Self::Concrete(_) => Ok(true),
            Self::User(TypeNode::Func(_), _) => Ok(false),
            _ => {
                if let Some(range) = self.ref_range(analyzer)? {
                    let min = range.evaled_range_min(analyzer, arena)?;
                    let max = range.evaled_range_max(analyzer, arena)?;
                    Ok(min.range_eq(&max, arena))
                } else {
                    Ok(false)
                }
            }
        }
    }

    pub fn func_node(&self, _analyzer: &impl GraphBackend) -> Option<FunctionNode> {
        match self {
            Self::User(TypeNode::Func(func_node), _) => Some(*func_node),
            _ => None,
        }
    }

    pub fn evaled_range(
        &self,
        analyzer: &impl GraphBackend,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Result<Option<(Elem<Concrete>, Elem<Concrete>)>, GraphError> {
        Ok(self.ref_range(analyzer)?.map(|range| {
            (
                range.evaled_range_min(analyzer, arena).unwrap(),
                range.evaled_range_max(analyzer, arena).unwrap(),
            )
        }))
    }

    // pub fn try_match_index_dynamic_ty(
    //     &self,
    //     index: ContextVarNode,
    //     analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    // ) -> Result<Option<NodeIdx>, GraphError> {
    //     match self {
    //         Self::BuiltIn(_node, None) => Ok(None),
    //         Self::BuiltIn(node, Some(r)) => {
    //             if let Builtin::Bytes(size) = node.underlying(analyzer)? {
    //                 if r.is_const(analyzer)? && index.is_const(analyzer)? {
    //                     let Some(min) = r.evaled_range_min(analyzer, arena)?.maybe_concrete() else {
    //                         return Ok(None);
    //                     };
    //                     let Concrete::Bytes(_, val) = min.val else {
    //                         return Ok(None);
    //                     };
    //                     let Some(idx) = index.evaled_range_min(analyzer, arena)?.unwrap().maybe_concrete()
    //                     else {
    //                         return Ok(None);
    //                     };
    //                     let Concrete::Uint(_, idx) = idx.val else {
    //                         return Ok(None);
    //                     };
    //                     if idx.low_u32() < (*size as u32) {
    //                         let mut h = B256::default();
    //                         h.0[0] = val.0[idx.low_u32() as usize];
    //                         let ret_val = Concrete::Bytes(1, h);
    //                         let node = analyzer.add_node(ret_val);
    //                         return Ok(Some(node));
    //                     }
    //                 }
    //                 Ok(None)
    //             } else {
    //                 // check if the index exists as a key
    //                 let min = r.range_min();
    //                 if let Some(map) = min.dyn_map() {
    //                     let name = index.name(analyzer)?;
    //                     let is_const = index.is_const(analyzer)?;
    //                     if let Some((_k, val)) = map.iter().find(|(k, _v)| match k {
    //                         Elem::Reference(Reference { idx, .. }) => match analyzer.node(*idx) {
    //                             Node::ContextVar(_) => {
    //                                 let cvar = ContextVarNode::from(*idx);
    //                                 cvar.name(analyzer).unwrap() == name
    //                             }
    //                             _ => false,
    //                         },
    //                         c @ Elem::Concrete(..) if is_const => {
    //                             let index_val = index.evaled_range_min(analyzer, arena).unwrap().unwrap();
    //                             index_val.range_eq(c)
    //                         }
    //                         _ => false,
    //                     }) {
    //                         if let Some(idx) = val.0.node_idx() {
    //                             return Ok(idx.into());
    //                         } else if let Some(c) = val.0.concrete() {
    //                             let cnode = analyzer.add_node(c);
    //                             return Ok(cnode.into());
    //                         }
    //                     }
    //                 }
    //                 Ok(None)
    //             }
    //         }
    //         Self::Concrete(node) => {
    //             if index.is_const(analyzer)? {
    //                 let idx = index
    //                     .evaled_range_min(analyzer, arena)
    //                     .unwrap()
    //                     .unwrap()
    //                     .concrete()
    //                     .unwrap()
    //                     .uint_val()
    //                     .unwrap();
    //                 match node.underlying(analyzer)? {
    //                     Concrete::Bytes(size, val) => {
    //                         if idx.low_u32() < (*size as u32) {
    //                             let mut h = B256::default();
    //                             h.0[0] = val.0[idx.low_u32() as usize];
    //                             let ret_val = Concrete::Bytes(1, h);
    //                             let node = analyzer.add_node(ret_val);
    //                             return Ok(Some(node));
    //                         }
    //                     }
    //                     Concrete::DynBytes(elems) => {
    //                         if idx.low_u32() < (elems.len() as u32) {
    //                             let mut h = B256::default();
    //                             h.0[0] = elems[idx.low_u32() as usize];
    //                             let ret_val = Concrete::Bytes(1, h);
    //                             let node = analyzer.add_node(ret_val);
    //                             return Ok(Some(node));
    //                         }
    //                     }
    //                     Concrete::String(st) => {
    //                         if idx.low_u32() < (st.len() as u32) {
    //                             let mut h = B256::default();
    //                             h.0[0] = st.as_bytes()[idx.low_u32() as usize];
    //                             let ret_val = Concrete::Bytes(1, h);
    //                             let node = analyzer.add_node(ret_val);
    //                             return Ok(Some(node));
    //                         }
    //                     }
    //                     Concrete::Array(elems) => {
    //                         if idx.low_u32() < (elems.len() as u32) {
    //                             let elem = &elems[idx.low_u32() as usize];
    //                             let node = analyzer.add_node(Node::Concrete(elem.clone()));
    //                             return Ok(Some(node));
    //                         }
    //                     }
    //                     _ => {}
    //                 }
    //             }
    //             Ok(None)
    //         }
    //         _ => Ok(None),
    //     }
    // }

    pub fn dynamic_underlying_ty(
        &self,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<VarType, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.dynamic_underlying_ty(analyzer),
            Self::Concrete(node) => node.dynamic_underlying_ty(analyzer),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin but it was: {e:?}"
            ))),
        }
    }

    pub fn is_mapping(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.is_mapping(analyzer)?),
            _ => Ok(false),
        }
    }

    pub fn is_sized_array(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.is_sized_array(analyzer),
            Self::Concrete(node) => node.is_sized_array(analyzer),
            _ => Ok(false),
        }
    }

    pub fn maybe_array_size(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<U256>, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.maybe_array_size(analyzer),
            Self::Concrete(node) => node.maybe_array_size(analyzer),
            _ => Ok(None),
        }
    }

    pub fn is_dyn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.is_dyn(analyzer)?),
            Self::Concrete(node) => Ok(node.is_dyn(analyzer)?),
            _ => Ok(false),
        }
    }

    pub fn is_indexable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.is_indexable(analyzer)?),
            Self::Concrete(node) => Ok(node.is_indexable(analyzer)?),
            _ => Ok(false),
        }
    }

    pub fn needs_length(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.needs_length(analyzer)?),
            Self::Concrete(node) => Ok(node.needs_length(analyzer)?),
            _ => Ok(false),
        }
    }

    pub fn ty_eq(&self, other: &Self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match (self, other) {
            (VarType::User(s, _), VarType::User(o, _)) => {
                Ok(s.unresolved_as_resolved(analyzer)? == o.unresolved_as_resolved(analyzer)?)
            }
            (VarType::BuiltIn(s, _), VarType::BuiltIn(o, _)) => {
                match (s.underlying(analyzer)?, o.underlying(analyzer)?) {
                    (Builtin::Array(l), Builtin::Array(r)) => l.ty_eq(r, analyzer),
                    (Builtin::SizedArray(l_size, l), Builtin::SizedArray(r_size, r)) => {
                        Ok(l.ty_eq(r, analyzer)? && l_size == r_size)
                    }
                    (Builtin::Mapping(lk, lv), Builtin::Mapping(rk, rv)) => {
                        Ok(lk.ty_eq(rk, analyzer)? && lv.ty_eq(rv, analyzer)?)
                    }
                    (l, r) => Ok(l == r),
                }
            }
            (VarType::Concrete(s), VarType::Concrete(o)) => Ok(s
                .underlying(analyzer)?
                .equivalent_ty(o.underlying(analyzer)?)),
            _ => Ok(false),
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        match self {
            VarType::User(ty_node, _) => ty_node.as_string(analyzer),
            VarType::BuiltIn(bn, _) => match analyzer.node(*bn) {
                Node::Builtin(bi) => bi.as_string(analyzer),
                _ => unreachable!(),
            },
            VarType::Concrete(c) => c.underlying(analyzer)?.as_builtin().as_string(analyzer),
        }
    }

    pub fn is_int(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.is_int()),
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.is_int()),
            _ => Ok(false),
        }
    }

    pub fn as_builtin(&self, analyzer: &impl GraphBackend) -> Result<Builtin, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.clone()),
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.as_builtin()),
            e => Err(GraphError::NodeConfusion(format!(
                "Expected to be builtin castable but wasnt: {e:?}"
            ))),
        }
    }

    pub fn maybe_struct(&self) -> Option<StructNode> {
        if let VarType::User(TypeNode::Struct(sn), _) = self {
            Some(*sn)
        } else {
            None
        }
    }

    pub fn maybe_err(&self) -> Option<ErrorNode> {
        if let VarType::User(TypeNode::Error(en), _) = self {
            Some(*en)
        } else {
            None
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum TypeNode {
    Contract(ContractNode),
    Struct(StructNode),
    Enum(EnumNode),
    Error(ErrorNode),
    Ty(TyNode),
    Func(FunctionNode),
    Unresolved(NodeIdx),
}

impl From<ContractNode> for TypeNode {
    fn from(c: ContractNode) -> Self {
        TypeNode::Contract(c)
    }
}

impl From<StructNode> for TypeNode {
    fn from(c: StructNode) -> Self {
        TypeNode::Struct(c)
    }
}

impl From<EnumNode> for TypeNode {
    fn from(c: EnumNode) -> Self {
        TypeNode::Enum(c)
    }
}

impl From<TyNode> for TypeNode {
    fn from(c: TyNode) -> Self {
        TypeNode::Ty(c)
    }
}

impl From<ErrorNode> for TypeNode {
    fn from(c: ErrorNode) -> Self {
        TypeNode::Error(c)
    }
}

impl From<FunctionNode> for TypeNode {
    fn from(c: FunctionNode) -> Self {
        TypeNode::Func(c)
    }
}

impl TypeNode {
    pub fn as_string(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
        match self {
            TypeNode::Contract(n) => Ok(format!("{} (Contract)", n.name(analyzer)?)),
            TypeNode::Struct(n) => Ok(format!("{} (Struct)", n.name(analyzer)?)),
            TypeNode::Enum(n) => Ok(format!("{} (Enum)", n.name(analyzer)?)),
            TypeNode::Error(n) => Ok(format!("{} (Error)", n.name(analyzer)?)),
            TypeNode::Ty(n) => Ok(format!("{} (Type Alias)", n.name(analyzer)?)),
            TypeNode::Func(n) => Ok(format!("function {}", n.name(analyzer)?)),
            TypeNode::Unresolved(n) => Ok(format!("UnresolvedType<{:?}>", analyzer.node(*n))),
        }
    }

    pub fn unresolved_as_resolved(&self, analyzer: &impl GraphBackend) -> Result<Self, GraphError> {
        match self {
            TypeNode::Unresolved(n) => match analyzer.node(*n) {
                Node::Unresolved(ident) => Err(GraphError::NodeConfusion(format!(
                    "Expected the type \"{}\" to be resolved by now",
                    ident.name
                ))),
                Node::Contract(..) => Ok(TypeNode::Contract((*n).into())),
                Node::Struct(..) => Ok(TypeNode::Struct((*n).into())),
                Node::Enum(..) => Ok(TypeNode::Enum((*n).into())),
                Node::Error(..) => Ok(TypeNode::Error((*n).into())),
                Node::Ty(..) => Ok(TypeNode::Ty((*n).into())),
                Node::Function(..) => Ok(TypeNode::Func((*n).into())),
                _ => Err(GraphError::NodeConfusion(
                    "Tried to type a non-typeable element".to_string(),
                )),
            },
            _ => Ok(*self),
        }
    }
}

impl From<TypeNode> for NodeIdx {
    fn from(val: TypeNode) -> Self {
        match val {
            TypeNode::Contract(n) => n.into(),
            TypeNode::Struct(n) => n.into(),
            TypeNode::Enum(n) => n.into(),
            TypeNode::Error(n) => n.into(),
            TypeNode::Ty(n) => n.into(),
            TypeNode::Func(n) => n.into(),
            TypeNode::Unresolved(n) => n,
        }
    }
}
