//! Solidity and EVM specific representations as nodes in the graph
use crate::analyzer::AsDotStr;
use crate::analyzer::GraphError;
use crate::analyzer::{AnalyzerLike, GraphLike};
use crate::range::elem::RangeElem;
use crate::range::elem_ty::Dynamic;
use crate::range::elem_ty::Elem;
use crate::range::elem_ty::RangeDyn;
use crate::range::Range;
use crate::range::SolcRange;
use crate::ContextVarNode;

use crate::Node;
use crate::NodeIdx;
use ethers_core::types::Address;
use ethers_core::types::H256;
use ethers_core::types::I256;
use ethers_core::types::U256;
use solang_parser::pt::{Expression, Loc, Type};

mod contract_ty;
pub use contract_ty::*;
mod enum_ty;
pub use enum_ty::*;
mod struct_ty;
pub use struct_ty::*;
mod func_ty;
pub use func_ty::*;
mod err_ty;
pub use err_ty::*;
mod var_ty;
pub use var_ty::*;
mod ty_ty;
pub use ty_ty::*;
mod concrete;
pub use concrete::*;
mod msg;
pub use msg::*;
mod block;
pub use block::*;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum VarType {
    User(TypeNode, Option<SolcRange>),
    BuiltIn(BuiltInNode, Option<SolcRange>),
    Concrete(ConcreteNode),
}

impl AsDotStr for VarType {
    fn as_dot_str(&self, analyzer: &impl GraphLike) -> String {
        self.as_string(analyzer).unwrap()
    }
}

impl VarType {
    pub fn set_range(&mut self, new_range: SolcRange) -> Result<(), GraphError> {
        match self {
            VarType::User(TypeNode::Enum(_), ref mut r)
            | VarType::User(TypeNode::Contract(_), ref mut r)
            | VarType::BuiltIn(_, ref mut r) => {
                *r = Some(new_range);
                Ok(())
            }
            _ => Err(GraphError::NodeConfusion(
                "This type cannot have a range".to_string(),
            )),
        }
    }

    pub fn is_dyn_builtin(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.is_dyn(analyzer),
            _ => Ok(false),
        }
    }

    pub fn concrete_to_builtin(
        &mut self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if let VarType::Concrete(cnode) = self {
            let c = cnode.underlying(analyzer)?.clone();
            match c {
                crate::Concrete::Uint(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Uint(*size))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::Int(ref size, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Int(*size))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::Bool(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bool)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::Address(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Address)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::Bytes(ref s, _) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::Bytes(*s))),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::String(_) => {
                    let new_ty = VarType::BuiltIn(
                        BuiltInNode::from(analyzer.builtin_or_add(Builtin::String)),
                        SolcRange::from(c),
                    );
                    *self = new_ty;
                }
                crate::Concrete::DynBytes(_) => {
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

    pub fn try_from_idx(analyzer: &(impl GraphLike + ?Sized), node: NodeIdx) -> Option<VarType> {
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
            Node::Enum(enu) => {
                let variants = enu.variants();
                let range = if !variants.is_empty() {
                    let min = Concrete::from(variants.first().unwrap().clone()).into();
                    let max = Concrete::from(variants.last().unwrap().clone()).into();
                    Some(SolcRange::new(min, max, vec![]))
                } else {
                    None
                };
                Some(VarType::User(TypeNode::Enum(node.into()), range))
            }
            Node::Concrete(_) => Some(VarType::Concrete(node.into())),
            Node::ContextVar(cvar) => Some(cvar.ty.clone()),
            Node::Var(var) => VarType::try_from_idx(analyzer, var.ty),
            Node::Ty(ty) => VarType::try_from_idx(analyzer, ty.ty),
            Node::Error(..)
            | Node::ContextFork
            | Node::FunctionCall
            | Node::FunctionParam(..)
            | Node::FunctionReturn(..)
            | Node::ErrorParam(..)
            | Node::Field(..)
            | Node::SourceUnitPart(..)
            | Node::SourceUnit(..)
            | Node::Entry
            | Node::Unresolved(..)
            | Node::Context(..)
            | Node::Msg(_)
            | Node::Block(_) => None,
        }
    }

    pub fn requires_input(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.requires_input()),
            _ => Ok(false),
        }
    }

    pub fn try_cast(
        self,
        other: &Self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<Self>, GraphError> {
        match (self, other) {
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
                if from_bn.implicitly_castable_to(to_bn, analyzer)? {
                    Ok(Some(Self::BuiltIn(*to_bn, sr)))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::BuiltIn(to_bn, _)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let b = to_bn.underlying(analyzer)?;
                if let Some(casted) = c.cast(b.clone()) {
                    let node = analyzer.add_node(Node::Concrete(casted));
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::Concrete(to_c)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let to_c = to_c.underlying(analyzer)?;
                if let Some(casted) = c.cast_from(to_c) {
                    let node = analyzer.add_node(Node::Concrete(casted));
                    Ok(Some(Self::Concrete(node.into())))
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
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<Self>, GraphError> {
        match (self, other) {
            (Self::BuiltIn(from_bn, sr), Self::BuiltIn(to_bn, _)) => {
                if from_bn.implicitly_castable_to(to_bn, analyzer)? {
                    Ok(Some(Self::BuiltIn(*to_bn, sr)))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::BuiltIn(to_bn, _)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let b = to_bn.underlying(analyzer)?;
                if let Some(casted) = c.literal_cast(b.clone()) {
                    let node = analyzer.add_node(Node::Concrete(casted));
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            (Self::Concrete(from_c), Self::Concrete(to_c)) => {
                let c = from_c.underlying(analyzer)?.clone();
                let to_c = to_c.underlying(analyzer)?;
                if let Some(casted) = c.literal_cast_from(to_c) {
                    let node = analyzer.add_node(Node::Concrete(casted));
                    Ok(Some(Self::Concrete(node.into())))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    pub fn implicitly_castable_to(
        &self,
        other: &Self,
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        match (self, other) {
            (Self::BuiltIn(from_bn, _), Self::BuiltIn(to_bn, _)) => {
                from_bn.implicitly_castable_to(to_bn, analyzer)
            }
            (Self::Concrete(from_c), Self::BuiltIn(_to_bn, _)) => {
                todo!("here, {from_c:?}")
            }
            _ => Ok(false),
        }
    }

    pub fn max_size(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
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

    pub fn range(&self, analyzer: &impl GraphLike) -> Result<Option<SolcRange>, GraphError> {
        match self {
            Self::User(_, Some(range)) => Ok(Some(range.clone())),
            Self::BuiltIn(_, Some(range)) => Ok(Some(range.clone())),
            Self::BuiltIn(bn, None) => Ok(SolcRange::try_from_builtin(bn.underlying(analyzer)?)),
            Self::Concrete(cnode) => Ok(SolcRange::from(cnode.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn delete_range_result(
        &self,
        analyzer: &impl GraphLike,
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
            Self::BuiltIn(bn, None) => bn.zero_range(analyzer),
            Self::Concrete(cnode) => Ok(cnode.underlying(analyzer)?.as_builtin().zero_range()),
            _ => Ok(None),
        }
    }

    pub fn default_range(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<SolcRange>, GraphError> {
        match self {
            Self::User(TypeNode::Contract(_), _) => {
                Ok(SolcRange::try_from_builtin(&Builtin::Address))
            }
            Self::User(TypeNode::Enum(enu), _) => enu.maybe_default_range(analyzer),
            Self::BuiltIn(bn, _) => Ok(SolcRange::try_from_builtin(bn.underlying(analyzer)?)),
            Self::Concrete(cnode) => Ok(SolcRange::from(cnode.underlying(analyzer)?.clone())),
            _ => Ok(None),
        }
    }

    pub fn is_const(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            Self::Concrete(_) => Ok(true),
            Self::User(TypeNode::Func(_), _) => Ok(false),
            _ => {
                if let Some(range) = self.range(analyzer)? {
                    let min = range.evaled_range_min(analyzer)?;
                    let max = range.evaled_range_max(analyzer)?;
                    Ok(min.range_eq(&max))
                } else {
                    Ok(false)
                }
            }
        }
    }

    pub fn func_node(&self, _analyzer: &impl GraphLike) -> Option<FunctionNode> {
        match self {
            Self::User(TypeNode::Func(func_node), _) => Some(*func_node),
            _ => None,
        }
    }

    pub fn evaled_range(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<(Elem<Concrete>, Elem<Concrete>)>, GraphError> {
        Ok(self.range(analyzer)?.map(|range| {
            (
                range.evaled_range_min(analyzer).unwrap(),
                range.evaled_range_max(analyzer).unwrap(),
            )
        }))
    }

    pub fn try_match_index_dynamic_ty(
        &self,
        index: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Option<NodeIdx>, GraphError> {
        match self {
            Self::BuiltIn(_node, None) => Ok(None),
            Self::BuiltIn(_node, Some(r)) => {
                // check if the index exists as a key
                let min = r.range_min();
                if let Some(map) = min.dyn_map() {
                    let name = index.name(analyzer)?;
                    let is_const = index.is_const(analyzer)?;
                    if let Some((_k, val)) = map.iter().find(|(k, _v)| match k {
                        Elem::Dynamic(Dynamic { idx, .. }) => match analyzer.node(*idx) {
                            Node::ContextVar(_) => {
                                let cvar = ContextVarNode::from(*idx);
                                cvar.name(analyzer).unwrap() == name
                            }
                            _ => false,
                        },
                        c @ Elem::Concrete(..) if is_const => {
                            let index_val = index.evaled_range_min(analyzer).unwrap().unwrap();
                            index_val.range_eq(c)
                        }
                        _ => false,
                    }) {
                        if let Some(idx) = val.node_idx() {
                            return Ok(idx.into());
                        } else if let Some(c) = val.concrete() {
                            let cnode = analyzer.add_node(Node::Concrete(c));
                            return Ok(cnode.into());
                        }
                    }
                }
                Ok(None)
            }
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin but it was: {e:?}"
            ))),
        }
    }

    pub fn get_index_dynamic_ty(
        &self,
        index: ContextVarNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<VarType, GraphError> {
        if let Some(var_ty) = self.try_match_index_dynamic_ty(index, analyzer)? {
            Ok(VarType::try_from_idx(analyzer, var_ty).unwrap())
        } else {
            match self {
                Self::BuiltIn(node, _) => node.dynamic_underlying_ty(analyzer),
                e => Err(GraphError::NodeConfusion(format!(
                    "Node type confusion: expected node to be Builtin but it was: {e:?}"
                ))),
            }
        }
    }

    pub fn dynamic_underlying_ty(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<VarType, GraphError> {
        match self {
            Self::BuiltIn(node, _) => node.dynamic_underlying_ty(analyzer),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin but it was: {e:?}"
            ))),
        }
    }

    pub fn is_mapping(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.is_mapping(analyzer)?),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be a Builtin but it was: {e:?}"
            ))),
        }
    }

    pub fn is_dyn(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            Self::BuiltIn(node, _) => Ok(node.is_dyn(analyzer)?),
            _ => Ok(false),
        }
    }

    pub fn ty_eq(&self, other: &Self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match (self, other) {
            (VarType::User(s, _), VarType::User(o, _)) => Ok(s == o),
            (VarType::BuiltIn(s, _), VarType::BuiltIn(o, _)) => {
                Ok(s.underlying(analyzer)? == o.underlying(analyzer)?)
            }
            (VarType::Concrete(s), VarType::Concrete(o)) => Ok(s
                .underlying(analyzer)?
                .equivalent_ty(o.underlying(analyzer)?)),
            _ => Ok(false),
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        match self {
            VarType::User(ty_node, _) => ty_node.as_string(analyzer),
            VarType::BuiltIn(bn, _) => match analyzer.node(*bn) {
                Node::Builtin(bi) => bi.as_string(analyzer),
                _ => unreachable!(),
            },
            VarType::Concrete(c) => c.underlying(analyzer)?.as_builtin().as_string(analyzer),
        }
    }

    pub fn is_int(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.is_int()),
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.is_int()),
            _ => Ok(false),
        }
    }

    pub fn as_builtin(&self, analyzer: &impl GraphLike) -> Result<Builtin, GraphError> {
        match self {
            VarType::BuiltIn(bn, _) => Ok(bn.underlying(analyzer)?.clone()),
            VarType::Concrete(c) => Ok(c.underlying(analyzer)?.as_builtin()),
            e => Err(GraphError::NodeConfusion(format!(
                "Expected to be builtin castable but wasnt: {e:?}"
            ))),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum TypeNode {
    Contract(ContractNode),
    Struct(StructNode),
    Enum(EnumNode),
    Func(FunctionNode),
}

impl TypeNode {
    pub fn as_string(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        match self {
            TypeNode::Contract(n) => n.name(analyzer),
            TypeNode::Struct(n) => n.name(analyzer),
            TypeNode::Enum(n) => n.name(analyzer),
            TypeNode::Func(n) => Ok(format!("function {}", n.name(analyzer)?)),
        }
    }
}

impl From<TypeNode> for NodeIdx {
    fn from(val: TypeNode) -> Self {
        match val {
            TypeNode::Contract(n) => n.into(),
            TypeNode::Struct(n) => n.into(),
            TypeNode::Enum(n) => n.into(),
            TypeNode::Func(n) => n.into(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct BuiltInNode(pub usize);

impl BuiltInNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> Result<&'a Builtin, GraphError> {
        match analyzer.node(*self) {
            Node::Builtin(b) => Ok(b),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin but it was: {e:?}"
            ))),
        }
    }

    pub fn num_size(&self, analyzer: &impl GraphLike) -> Result<Option<u16>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.num_size())
    }

    pub fn implicitly_castable_to(
        &self,
        other: &Self,
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .implicitly_castable_to(other.underlying(analyzer)?))
    }

    pub fn max_size(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<Self, GraphError> {
        let m = self.underlying(analyzer)?.max_size();
        Ok(analyzer.builtin_or_add(m).into())
    }

    pub fn dynamic_underlying_ty(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<VarType, GraphError> {
        match self.underlying(analyzer)? {
            Builtin::Array(v_ty) => Ok(v_ty.clone()),
            Builtin::Mapping(_, v_ty) => Ok(v_ty.clone()),
            Builtin::DynamicBytes => Ok(VarType::BuiltIn(
                analyzer.builtin_or_add(Builtin::Bytes(1)).into(),
                Some(SolcRange::new(
                    Elem::from(Concrete::from(vec![0x00])),
                    Elem::from(Concrete::from(vec![0xff])),
                    vec![],
                )),
            )),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin::Array but it was: {e:?}"
            ))),
        }
    }

    pub fn is_mapping(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(self.underlying(analyzer)?, Builtin::Mapping(_, _)))
    }

    pub fn is_dyn(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_dyn())
    }

    pub fn zero_range(&self, analyzer: &impl GraphLike) -> Result<Option<SolcRange>, GraphError> {
        Ok(self.underlying(analyzer)?.zero_range())
    }
}

impl From<NodeIdx> for BuiltInNode {
    fn from(idx: NodeIdx) -> Self {
        BuiltInNode(idx.index())
    }
}

impl From<BuiltInNode> for NodeIdx {
    fn from(val: BuiltInNode) -> Self {
        val.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Builtin {
    Address,
    AddressPayable,
    Payable,
    Bool,
    String,
    Int(u16),
    Uint(u16),
    Bytes(u8),
    Rational,
    DynamicBytes,
    Array(VarType),
    Mapping(VarType, VarType),
    Func(Vec<VarType>, Vec<VarType>),
}

impl Builtin {
    pub fn zero_range(&self) -> Option<SolcRange> {
        match self {
            Builtin::Address | Builtin::AddressPayable | Builtin::Payable => {
                let zero = Concrete::Address(Address::from_slice(&[0x00; 20]));
                Some(SolcRange::new(zero.clone().into(), zero.into(), vec![]))
            }
            Builtin::Bool => SolcRange::from(Concrete::from(false)),
            Builtin::String => SolcRange::from(Concrete::from("".to_string())),
            Builtin::Int(_) => SolcRange::from(Concrete::from(I256::from(0))),
            Builtin::Uint(_) => SolcRange::from(Concrete::from(U256::from(0))),
            Builtin::Bytes(s) => SolcRange::from(Concrete::Bytes(*s, H256::zero())),
            Builtin::DynamicBytes | Builtin::Array(_) | Builtin::Mapping(_, _) => {
                let zero = Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(U256::zero())),
                    val: Default::default(),
                    loc: Loc::Implicit,
                }));
                Some(SolcRange::new(zero.clone(), zero, vec![]))
            }
            Builtin::Rational | Builtin::Func(_, _) => None,
        }
    }
    pub fn try_from_ty(
        ty: Type,
        analyzer: &mut (impl GraphLike + AnalyzerLike<Expr = Expression>),
    ) -> Option<Builtin> {
        use Type::*;
        match ty {
            Address => Some(Builtin::Address),
            AddressPayable => Some(Builtin::AddressPayable),
            Payable => Some(Builtin::Payable),
            Bool => Some(Builtin::Bool),
            String => Some(Builtin::String),
            Int(size) => Some(Builtin::Int(size)),
            Uint(size) => Some(Builtin::Uint(size)),
            Bytes(size) => Some(Builtin::Bytes(size)),
            Rational => Some(Builtin::Rational),
            DynamicBytes => Some(Builtin::DynamicBytes),
            Mapping { key, value, .. } => {
                let key_idx = analyzer.parse_expr(&key);
                let val_idx = analyzer.parse_expr(&value);
                let key_var_ty = VarType::try_from_idx(analyzer, key_idx)?;
                let val_var_ty = VarType::try_from_idx(analyzer, val_idx)?;
                Some(Builtin::Mapping(key_var_ty, val_var_ty))
            }
            Function {
                params,
                attributes: _,
                returns,
            } => {
                let inputs = params
                    .iter()
                    .filter_map(|(_, param)| param.as_ref())
                    .map(|param| analyzer.parse_expr(&param.ty))
                    .collect::<Vec<_>>();
                let inputs = inputs
                    .iter()
                    .map(|idx| VarType::try_from_idx(analyzer, *idx).expect("Couldn't parse param"))
                    .collect::<Vec<_>>();
                let mut outputs = vec![];
                if let Some((params, _attrs)) = returns {
                    let tmp_outputs = params
                        .iter()
                        .filter_map(|(_, param)| param.as_ref())
                        .map(|param| analyzer.parse_expr(&param.ty))
                        .collect::<Vec<_>>();
                    outputs = tmp_outputs
                        .iter()
                        .map(|idx| {
                            VarType::try_from_idx(analyzer, *idx)
                                .expect("Couldn't parse output param")
                        })
                        .collect::<Vec<_>>();
                }
                Some(Builtin::Func(inputs, outputs))
            }
        }
    }

    pub fn is_dyn(&self) -> bool {
        matches!(
            self,
            Builtin::DynamicBytes | Builtin::Array(..) | Builtin::Mapping(..) | Builtin::String
        )
    }

    pub fn requires_input(&self) -> bool {
        matches!(self, Builtin::Array(..) | Builtin::Mapping(..))
    }

    pub fn num_size(&self) -> Option<u16> {
        match self {
            Builtin::Uint(size) => Some(*size),
            Builtin::Int(size) => Some(*size),
            _ => None,
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Builtin::Int(_))
    }

    pub fn implicitly_castable_to(&self, other: &Self) -> bool {
        use Builtin::*;
        match (self, other) {
            (Address, Address) => true,
            (AddressPayable, Address) => true,
            (Payable, Address) => true,
            (Bool, Bool) => true,
            (Rational, Rational) => true,
            (DynamicBytes, DynamicBytes) => true,
            (String, String) => true,
            (Uint(from_size), Uint(to_size)) => from_size <= to_size,
            (Int(from_size), Int(to_size)) => from_size <= to_size,
            (Bytes(from_size), Bytes(to_size)) => from_size <= to_size,
            _ => false,
        }
    }

    pub fn max_size(&self) -> Self {
        use Builtin::*;
        match self {
            Uint(_) => Uint(256),
            Int(_from_size) => Uint(256),
            Bytes(_from_size) => Uint(32),
            _ => self.clone(),
        }
    }

    pub fn as_string(&self, analyzer: &impl GraphLike) -> Result<String, GraphError> {
        use Builtin::*;
        match self {
            Address => Ok("address".to_string()),
            AddressPayable => Ok("address".to_string()),
            Payable => Ok("address".to_string()),
            Bool => Ok("bool".to_string()),
            String => Ok("string".to_string()),
            Int(size) => Ok(format!("int{size}")),
            Uint(size) => Ok(format!("uint{size}")),
            Bytes(size) => Ok(format!("bytes{size}")),
            Rational => Ok("rational".to_string()),
            DynamicBytes => Ok("bytes".to_string()),
            Array(v_ty) => Ok(format!("{}[]", v_ty.as_string(analyzer)?)),
            Mapping(key_ty, v_ty) => Ok(format!(
                "mapping ({} => {})",
                key_ty.as_string(analyzer)?,
                v_ty.as_string(analyzer)?
            )),
            Func(inputs, outputs) => Ok(format!(
                "function({}) returns ({})",
                inputs
                    .iter()
                    .map(|input| input.as_string(analyzer).unwrap())
                    .collect::<Vec<_>>()
                    .join(", "),
                outputs
                    .iter()
                    .map(|output| output.as_string(analyzer).unwrap())
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        }
    }
}
