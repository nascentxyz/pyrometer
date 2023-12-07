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

    pub fn is_mapping(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(self.underlying(analyzer)?, Builtin::Mapping(_, _)))
    }

    pub fn is_sized_array(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?,
            Builtin::SizedArray(_, _)
        ))
    }

    pub fn maybe_array_size(&self, analyzer: &impl GraphLike) -> Result<Option<U256>, GraphError> {
        match self.underlying(analyzer)? {
            Builtin::SizedArray(s, _) => Ok(Some(*s)),
            Builtin::Bytes(s) => Ok(Some(U256::from(*s))),
            _ => Ok(None),
        }
    }

    pub fn is_dyn(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_dyn())
    }

    pub fn is_indexable(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_indexable())
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
    SizedArray(U256, VarType),
    Mapping(VarType, VarType),
    Func(Vec<VarType>, Vec<VarType>),
}

impl Builtin {
    pub fn unresolved_as_resolved(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
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

    pub fn requires_input(&self) -> bool {
        matches!(
            self,
            Builtin::Array(..) | Builtin::SizedArray(..) | Builtin::Mapping(..)
        )
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