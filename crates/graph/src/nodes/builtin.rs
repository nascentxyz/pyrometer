use crate::{AnalyzerBackend, GraphBackend, SolcRange, VarType, Node, GraphError, nodes::Concrete};

use shared::NodeIdx;
use crate::range::elem::*;

use solang_parser::pt::{Type, Expression, Loc};
use ethers_core::types::{Address, H256, U256, I256};

/// A builtin node
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct BuiltInNode(pub usize);

impl BuiltInNode {
    /// Gets the underlying builtin from the graph
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Builtin, GraphError> {
        match analyzer.node(*self) {
            Node::Builtin(b) => Ok(b),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Builtin but it was: {e:?}"
            ))),
        }
    }

    /// Gets the size of the builtin
    pub fn num_size(&self, analyzer: &impl GraphBackend) -> Result<Option<u16>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.num_size())
    }

    /// Checks if this builtin is implicitly castable to another builtin
    pub fn implicitly_castable_to(
        &self,
        other: &Self,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        Ok(self
            .underlying(analyzer)?
            .implicitly_castable_to(other.underlying(analyzer)?))
    }

    /// Gets the maximum size version of this builtin, i.e. uint16 -> uint256
    pub fn max_size(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        let m = self.underlying(analyzer)?.max_size();
        Ok(analyzer.builtin_or_add(m).into())
    }

    /// Gets the underlying type of the dynamic builtin backing it. i.e. uint256[] -> uint256
    pub fn dynamic_underlying_ty(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<VarType, GraphError> {
        match self.underlying(analyzer)? {
            Builtin::Array(v_ty) | Builtin::SizedArray(_, v_ty) => {
                v_ty.unresolved_as_resolved(analyzer)
            }
            Builtin::Mapping(_, v_ty) => v_ty.unresolved_as_resolved(analyzer),
            Builtin::DynamicBytes | Builtin::Bytes(_) => Ok(VarType::BuiltIn(
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

    /// Returns whether the builtin is a mapping
    pub fn is_mapping(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(self.underlying(analyzer)?, Builtin::Mapping(_, _)))
    }

    /// Returns whether the builtin is a sized array
    pub fn is_sized_array(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?,
            Builtin::SizedArray(_, _)
        ))
    }

    /// Returns whether the builtin is a sized array or bytes
    pub fn maybe_array_size(&self, analyzer: &impl GraphBackend) -> Result<Option<U256>, GraphError> {
        match self.underlying(analyzer)? {
            Builtin::SizedArray(s, _) => Ok(Some(*s)),
            Builtin::Bytes(s) => Ok(Some(U256::from(*s))),
            _ => Ok(None),
        }
    }

    /// Returns whether the builtin is a dynamic type
    pub fn is_dyn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_dyn())
    }

    /// Returns whether the builtin is indexable
    pub fn is_indexable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_indexable())
    }

    /// Returns the zero range for this builtin type, i.e. uint256 -> [0, 0]
    pub fn zero_range(&self, analyzer: &impl GraphBackend) -> Result<Option<SolcRange>, GraphError> {
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

/// A fundamental builtin type
#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Builtin {
    /// An address
    Address,
    /// A payable address
    AddressPayable,
    /// A payable address, differentiated in Solang so we differentiate
    Payable,
    /// A boolean
    Bool,
    /// A string - TODO: we should represent this as bytes internally
    String,
    /// A signed integer that has a size
    Int(u16),
    /// An unsigned integer that has a size
    Uint(u16),
    /// A bytes that has a size, i.e. bytes8
    Bytes(u8),
    /// A rational. Rarely used in practice
    Rational,
    /// A byte array, i.e. bytes
    DynamicBytes,
    /// An array that has an internal type, i.e. uint256[]
    Array(VarType),
    /// An array that has an internal type and is sized, i.e. uint256[5]
    SizedArray(U256, VarType),
    /// A mapping, i.e. `mapping (address => uint)`
    Mapping(VarType, VarType),
    /// A function pointer that takes a vector of types and returns a vector of types
    Func(Vec<VarType>, Vec<VarType>),
}

impl Builtin {
    /// Resolves the `VarType` in dynamic builtins due to parse order - i.e. we could
    /// `mapping (uint => MyType)`, we may not have parsed `MyType`, so we now try to resolve it
    pub fn unresolved_as_resolved(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        match self {
            Builtin::Array(n) => Ok(Builtin::Array(n.unresolved_as_resolved(analyzer)?)),
            Builtin::SizedArray(s, n) => {
                Ok(Builtin::SizedArray(*s, n.unresolved_as_resolved(analyzer)?))
            }
            Builtin::Mapping(k, v) => Ok(Builtin::Mapping(
                k.unresolved_as_resolved(analyzer)?,
                v.unresolved_as_resolved(analyzer)?,
            )),
            _ => Ok(self.clone()),
        }
    }

    /// Possible types that this type could have been had a literal been parsed differently - i.e. a `1` 
    /// could be uint8 to uint256.
    pub fn possible_builtins_from_ty_inf(&self) -> Vec<Builtin> {
        let mut builtins = vec![];
        match self {
            Builtin::Uint(size) => {
                let mut s = *size;
                while s > 0 {
                    builtins.push(Builtin::Uint(s));
                    s -= 8;
                }
            }
            Builtin::Int(size) => {
                let mut s = *size;
                while s > 0 {
                    builtins.push(Builtin::Int(s));
                    s -= 8;
                }
            }
            Builtin::Bytes(size) => {
                let mut s = *size;
                while s > 0 {
                    builtins.push(Builtin::Bytes(s));
                    s -= 1;
                }
            }
            _ => {}
        }
        builtins
    }

    /// Construct a [`SolcRange`] that is zero
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
            Builtin::SizedArray(s, _) => {
                let sized = Elem::ConcreteDyn(Box::new(RangeDyn {
                    minimized: None,
                    maximized: None,
                    len: Elem::from(Concrete::from(*s)),
                    val: Default::default(),
                    loc: Loc::Implicit,
                }));
                Some(SolcRange::new(sized.clone(), sized, vec![]))
            }
            Builtin::Rational | Builtin::Func(_, _) => None,
        }
    }

    /// Try to convert from a [`Type`] to a Builtin
    pub fn try_from_ty(
        ty: Type,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend<Expr = Expression>),
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
                let key_idx = analyzer.parse_expr(&key, None);
                let val_idx = analyzer.parse_expr(&value, None);
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
                    .map(|param| analyzer.parse_expr(&param.ty, None))
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
                        .map(|param| analyzer.parse_expr(&param.ty, None))
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

    /// Returns whether the builtin is dynamic
    pub fn is_dyn(&self) -> bool {
        matches!(
            self,
            Builtin::DynamicBytes
                | Builtin::Array(..)
                | Builtin::SizedArray(..)
                | Builtin::Mapping(..)
                | Builtin::String
        )
    }

    /// Returns whether the builtin requires input to perform an operation on (like addition)
    pub fn requires_input(&self) -> bool {
        matches!(
            self,
            Builtin::Array(..) | Builtin::SizedArray(..) | Builtin::Mapping(..)
        )
    }

    /// Returns the size of the integer if it is an integer (signed or unsigned)
    pub fn num_size(&self) -> Option<u16> {
        match self {
            Builtin::Uint(size) => Some(*size),
            Builtin::Int(size) => Some(*size),
            _ => None,
        }
    }

    /// Returns whether the builtin is a signed integer
    pub fn is_int(&self) -> bool {
        matches!(self, Builtin::Int(_))
    }

    /// Returns whether the builtin is indexable (bytes, array[], array[5], mapping(..), bytes32, string)
    pub fn is_indexable(&self) -> bool {
        matches!(
            self,
            Builtin::DynamicBytes
                | Builtin::Array(..)
                | Builtin::SizedArray(..)
                | Builtin::Mapping(..)
                | Builtin::Bytes(..)
                | Builtin::String
        )
    }

    /// Checks if self is implicitly castable to another builtin
    pub fn implicitly_castable_to(&self, other: &Self) -> bool {
        use Builtin::*;
        match (self, other) {
            (Address, Address) => true,
            (Address, AddressPayable) => true,
            (Address, Payable) => true,
            (AddressPayable, Address) => true,
            (AddressPayable, Payable) => true,
            (AddressPayable, AddressPayable) => true,
            (Payable, Address) => true,
            (Payable, AddressPayable) => true,
            (Payable, Payable) => true,
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

    /// Returns the max size version of this builtin
    pub fn max_size(&self) -> Self {
        use Builtin::*;
        match self {
            Uint(_) => Uint(256),
            Int(_from_size) => Uint(256),
            Bytes(_from_size) => Uint(32),
            _ => self.clone(),
        }
    }

    /// Converts the builtin to a string
    pub fn as_string(&self, analyzer: &impl GraphBackend) -> Result<String, GraphError> {
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
            Array(v_ty) => Ok(format!(
                "{}[]",
                v_ty.unresolved_as_resolved(analyzer)?.as_string(analyzer)?
            )),
            SizedArray(s, v_ty) => Ok(format!(
                "{}[{}]",
                v_ty.unresolved_as_resolved(analyzer)?.as_string(analyzer)?,
                s
            )),
            Mapping(key_ty, v_ty) => Ok(format!(
                "mapping ({} => {})",
                key_ty
                    .unresolved_as_resolved(analyzer)?
                    .as_string(analyzer)?,
                v_ty.unresolved_as_resolved(analyzer)?.as_string(analyzer)?
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

    /// Converts the builtin to a string if it is not dynamic
    pub fn basic_as_string(&self) -> String {
        use Builtin::*;
        match self {
            Address => "address".to_string(),
            AddressPayable => "address".to_string(),
            Payable => "address".to_string(),
            Bool => "bool".to_string(),
            String => "string".to_string(),
            Int(size) => format!("int{size}"),
            Uint(size) => format!("uint{size}"),
            Bytes(size) => format!("bytes{size}"),
            Rational => "rational".to_string(),
            DynamicBytes => "bytes".to_string(),
            Array(_v_ty) => "<user type>[]".to_string(),
            SizedArray(s, _v_ty) => format!("<user type>[{}]", s),
            Mapping(_key_ty, _v_ty) => "mapping (<user type> => <user type>)".to_string(),
            Func(inputs, outputs) => format!(
                "function({}) returns ({})",
                inputs
                    .iter()
                    .map(|_input| "<user type>")
                    .collect::<Vec<_>>()
                    .join(", "),
                outputs
                    .iter()
                    .map(|_output| "<user type>")
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}