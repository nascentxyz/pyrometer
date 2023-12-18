use crate::{nodes::Builtin, AnalyzerBackend, GraphBackend, GraphError, Node, VarType};
use shared::NodeIdx;

use ethers_core::types::{Address, H256, I256, U256};

/// An index in the graph that references a [`Concrete`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConcreteNode(pub usize);

impl ConcreteNode {
    /// Gets the underlying node data for the [`Concrete`]
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a Concrete, GraphError> {
        match analyzer.node(*self) {
            Node::Concrete(c) => Ok(c),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Concrete but it was: {e:?}"
            ))),
        }
    }

    /// Creates a version of this concrete that is max size
    pub fn max_size(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<Self, GraphError> {
        let c = self.underlying(analyzer)?.max_size();
        Ok(analyzer.add_node(Node::Concrete(c)).into())
    }

    /// Gets the internal type of the dynamic that backs this. Panics if this is not a dynamic concrete
    pub fn dynamic_underlying_ty(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<VarType, GraphError> {
        let builtin = self.underlying(analyzer)?.dynamic_underlying_ty().unwrap();
        let bn = analyzer.builtin_or_add(builtin);
        let v_ty = VarType::try_from_idx(analyzer, bn).unwrap();
        Ok(v_ty)
    }

    /// Returns whether this is a dynamic concrete
    pub fn is_dyn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_dyn())
    }

    /// Returns whether this is a concrete sized array
    pub fn is_sized_array(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_sized_array())
    }

    /// Returns the size of the array size if it is an array-like concrete
    pub fn maybe_array_size(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<U256>, GraphError> {
        Ok(self.underlying(analyzer)?.maybe_array_size())
    }

    /// Returns whether this concrete is indexable
    pub fn is_indexable(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_indexable())
    }
}

impl From<NodeIdx> for ConcreteNode {
    fn from(idx: NodeIdx) -> Self {
        ConcreteNode(idx.index())
    }
}

impl From<ConcreteNode> for NodeIdx {
    fn from(val: ConcreteNode) -> Self {
        val.0.into()
    }
}

/// EVM/Solidity basic concrete types
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Concrete {
    /// An unsigned integer, in the form of (bits, value)
    Uint(u16, U256),
    /// A signed integer, in the form of (bits, value)
    Int(u16, I256),
    /// An fixed length bytes, in the form of (bytes, value)
    Bytes(u8, H256),
    /// A 20 byte address
    Address(Address),
    /// A boolean
    Bool(bool),
    /// A vector of bytes
    DynBytes(Vec<u8>),
    /// A string, (TODO: solidity doesn't enforce utf-8 encoding like rust. Likely this type
    /// should be modeled with a `Vec<u8>` instead.)
    String(String),
    /// An array of concrete values
    Array(Vec<Concrete>),
}

// impl From<usize> for Concrete {
//     fn from(u: usize) -> Self {
//         Concrete::Uint(256, U256::from(u))
//     }
// }

impl From<U256> for Concrete {
    fn from(u: U256) -> Self {
        Concrete::Uint(256, u)
    }
}

impl From<I256> for Concrete {
    fn from(u: I256) -> Self {
        Concrete::Int(256, u)
    }
}

impl From<Vec<u8>> for Concrete {
    fn from(u: Vec<u8>) -> Self {
        Concrete::DynBytes(u)
    }
}

impl From<H256> for Concrete {
    fn from(u: H256) -> Self {
        Concrete::Bytes(32, u)
    }
}

impl<const N: usize> From<[u8; N]> for Concrete {
    fn from(u: [u8; N]) -> Self {
        assert!(N <= 32);
        let mut h = H256::default();
        h.assign_from_slice(&u[..]);
        Concrete::Bytes(N.try_into().unwrap(), h)
    }
}

impl From<Address> for Concrete {
    fn from(u: Address) -> Self {
        Concrete::Address(u)
    }
}

impl From<bool> for Concrete {
    fn from(u: bool) -> Self {
        Concrete::Bool(u)
    }
}

impl From<String> for Concrete {
    fn from(u: String) -> Self {
        Concrete::String(u)
    }
}

impl<T: Into<Concrete>> From<Vec<T>> for Concrete {
    fn from(u: Vec<T>) -> Self {
        Concrete::Array(u.into_iter().map(|t| t.into()).collect())
    }
}

impl Concrete {
    pub fn set_indices(&mut self, other: &Self) {
        match (self, other) {
            (Concrete::DynBytes(s), Concrete::DynBytes(o)) => {
                o.iter().enumerate().for_each(|(i, b)| {
                    s[i] = *b;
                });
            }
            (Concrete::Array(s), Concrete::Array(o)) => {
                o.iter().enumerate().for_each(|(i, b)| {
                    s[i] = b.clone();
                });
            }
            (Concrete::String(s), Concrete::String(o)) => {
                o.chars().enumerate().for_each(|(i, b)| {
                    s.replace_range(i..i+1, &b.to_string());
                });
            }
            (Concrete::Bytes(size, s), Concrete::Bytes(cap, o)) => {
                let mut bytes = [0u8; 32];
                s.0.into_iter()
                    .take((*size).into())
                    .enumerate()
                    .for_each(|(i, b)| bytes[i] = b);
                o.0.into_iter()
                    .take((*cap).into())
                    .enumerate()
                    .for_each(|(i, b)| bytes[i] = b);
                *s = H256(bytes);
            }
            _ => {}
        }
    }

    pub fn get_index(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Concrete::DynBytes(s), Concrete::Uint(_, o)) => {
                let index = o.as_usize();
                let mut bytes = [0u8; 32];
                bytes[0] = s[index];
                Some(Concrete::Bytes(1, H256(bytes)))
            }
            (Concrete::Array(s), Concrete::Uint(_, o)) => {
                let index = o.as_usize();
                Some(s[index].clone())
            }
            (Concrete::String(s), Concrete::Uint(_, o)) => {
                let index = o.as_usize();
                Some(Concrete::String(s[index..index+1].to_string()))
            }
            (Concrete::Bytes(size, s), Concrete::Uint(_, o)) => {
                let index = o.as_usize();
                let mut bytes = [0u8; 32];
                bytes[0] = s[index];
                Some(Concrete::Bytes(1, H256(bytes)))
            }
            _ => None
        }
    }

    /// Returns whether this concrete is a dynamic type
    pub fn is_dyn(&self) -> bool {
        matches!(
            self,
            Concrete::DynBytes(..) | Concrete::String(..) | Concrete::Array(..)
        )
    }

    /// Returns whether this concrete is a sized array
    pub fn is_sized_array(&self) -> bool {
        matches!(self, Concrete::DynBytes(..) | Concrete::Array(..))
    }

    /// Returns the internal type of this dynamic concrete
    pub fn dynamic_underlying_ty(&self) -> Option<Builtin> {
        match self {
            Concrete::DynBytes(_v) => Some(Builtin::Bytes(1)),
            Concrete::Array(v) => v.first().map(|inner| inner.as_builtin()),
            Concrete::String(_v) => Some(Builtin::Bytes(1)),
            Concrete::Bytes(_, _) => Some(Builtin::Bytes(1)),
            _ => None,
        }
    }

    /// Returns the length of the array if it is an array
    pub fn maybe_array_size(&self) -> Option<U256> {
        match self {
            Concrete::DynBytes(v) => Some(U256::from(v.len())),
            Concrete::Array(v) => Some(U256::from(v.len())),
            Concrete::String(v) => Some(U256::from(v.len())),
            Concrete::Bytes(s, _) => Some(U256::from(*s)),
            _ => None,
        }
    }

    /// Returns whether this concrete is indexable
    pub fn is_indexable(&self) -> bool {
        self.is_dyn() || matches!(self, Concrete::Bytes(..))
    }

    /// Convert a U256 back into it's original type. This is used mostly
    /// for range calculations to improve ergonomics. Basically
    /// the EVM only operates on U256 words, so most of this should
    /// be fine.
    pub fn u256_as_original(&self, uint: U256) -> Self {
        match self {
            Concrete::Uint(size, _) => Concrete::Uint(256, uint)
                .cast(Builtin::Uint(*size))
                .unwrap(),
            Concrete::Int(size, _) => Concrete::Int(256, I256::from_raw(uint))
                .cast(Builtin::Int(*size))
                .unwrap(),
            Concrete::Bytes(size, _) => {
                let mut h = H256::default();
                uint.to_big_endian(h.as_mut());
                Concrete::Bytes(32, h).cast(Builtin::Bytes(*size)).unwrap()
            }
            Concrete::Address(_) => {
                let mut bytes = [0u8; 32];
                uint.to_big_endian(&mut bytes);
                Concrete::Address(Address::from_slice(&bytes[12..]))
            }
            Concrete::Bool(_) => {
                if uint > U256::zero() {
                    Concrete::Bool(true)
                } else {
                    Concrete::Bool(false)
                }
            }
            Concrete::DynBytes(v) => {
                let mut bytes = [0u8; 32];
                uint.to_big_endian(&mut bytes);
                let new_vec = &bytes.to_vec()[0..v.len()];
                Concrete::DynBytes(new_vec.to_vec())
            }
            e => todo!("Unsupported: {e:?}"),
        }
    }

    /// Cast from one concrete variant given another concrete variant
    pub fn cast_from(self, other: &Self) -> Option<Self> {
        self.cast(other.as_builtin())
    }

    /// Cast from one concrete variant given another concrete variant, but since its a literal
    /// uint to bytesX are right padded
    pub fn literal_cast_from(self, other: &Self) -> Option<Self> {
        self.literal_cast(other.as_builtin())
    }

    pub fn equivalent_ty(&self, other: &Self) -> bool {
        match (self, other) {
            (Concrete::Uint(size, _), Concrete::Uint(other_size, _)) if size == other_size => true,
            (Concrete::Int(size, _), Concrete::Int(other_size, _)) if size == other_size => true,
            (Concrete::Bytes(size, _), Concrete::Bytes(other_size, _)) if size == other_size => {
                true
            }
            (Concrete::Address(_), Concrete::Address(_)) => true,
            (Concrete::Bool(_), Concrete::Bool(_)) => true,
            (Concrete::DynBytes(_), Concrete::DynBytes(_)) => true,
            (Concrete::String(_), Concrete::String(_)) => true,
            (Concrete::Array(v0), Concrete::Array(v1)) => {
                if v0.is_empty() || v1.is_empty() {
                    true
                } else {
                    v0[0].equivalent_ty(&v1[0])
                }
            }
            _ => false,
        }
    }

    /// Returns whether this concrete is an unsigned integer
    pub fn is_int(&self) -> bool {
        matches!(self, Concrete::Int(_, _))
    }

    /// Performs a literal cast to another type
    pub fn literal_cast(self, builtin: Builtin) -> Option<Self> {
        match self {
            Concrete::Uint(_, val) => match builtin {
                Builtin::Bytes(size) => {
                    let mask = if size == 32 {
                        U256::MAX
                    } else {
                        U256::from(2).pow((size as u16 * 8).into()) - 1
                    };

                    let h = H256::from_slice(
                        &(val & mask)
                            .0
                            .iter()
                            .flat_map(|v| v.to_le_bytes())
                            .collect::<Vec<_>>()[..],
                    );
                    Some(Concrete::Bytes(size, h))
                }
                _ => self.cast(builtin),
            },
            _ => self.cast(builtin),
        }
    }

    /// Concatenate two concretes together
    pub fn concat(self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Concrete::String(a), Concrete::String(b)) => Some(Concrete::from(format!("{a}{b}"))),
            (Concrete::DynBytes(mut a), Concrete::DynBytes(b)) => {
                a.extend(b);
                Some(Concrete::from(a))
            }
            _ => None,
        }
    }

    pub fn bit_representation(&self) -> Option<Concrete> {
        match self {
            Concrete::Int(size, val) => {
                let mut bytes = [0u8; 32];
                val.to_big_endian(&mut bytes);
                Some(Concrete::Uint(*size, U256::from_big_endian(&bytes)))
            }
            Concrete::Bytes(size, _) => Some(Concrete::Uint(*size as u16 / 8, self.into_u256().unwrap())),
            Concrete::Bool(_val) => Some(Concrete::Uint(8, self.into_u256().unwrap())),
            Concrete::Address(_val) => Some(Concrete::Uint(20, self.into_u256().unwrap())),
            _ => None
        }
    }

    /// Cast the concrete to another type as denoted by a [`Builtin`].
    pub fn cast(self, builtin: Builtin) -> Option<Self> {
        match self {
            Concrete::Uint(r_size, val) => {
                match builtin {
                    Builtin::Address => {
                        let mut bytes = [0u8; 32];
                        val.to_big_endian(&mut bytes);
                        Some(Concrete::Address(Address::from_slice(&bytes[12..])))
                    }
                    Builtin::Uint(size) => {
                        // no op
                        if r_size == size {
                            Some(self)
                        } else {
                            let mask = if size == 256 {
                                U256::MAX
                            } else {
                                U256::from(2).pow(size.into()) - 1
                            };
                            if val < mask {
                                Some(Concrete::Uint(size, val))
                            } else {
                                Some(Concrete::Uint(size, val & mask))
                            }
                        }
                    }
                    Builtin::Int(size) => {
                        Some(Concrete::Int(size, I256::from_raw(val)))
                    },
                    Builtin::Bytes(size) => {
                        let mask = if size == 32 {
                            U256::MAX
                        } else {
                            let v = U256::from(2).pow((size as u16 * 8).into()) - 1;
                            v << v.leading_zeros()
                        };

                        // let h = H256::from_slice(&(val & mask).0.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<_>>()[..]);
                        let mut h = H256::default();
                        (val & mask).to_big_endian(&mut h.0);
                        Some(Concrete::Bytes(size, h))
                    }
                    Builtin::Bool => {
                        if val > U256::zero() {
                            Some(Concrete::from(true))
                        } else {
                            Some(Concrete::from(false))
                        }
                    }
                    _ => None,
                }
            }
            Concrete::Int(r_size, val) => match builtin {
                Builtin::Address => {
                    let mut bytes = [0u8; 32];
                    val.to_big_endian(&mut bytes);
                    Some(Concrete::Address(Address::from_slice(&bytes[12..])))
                }
                Builtin::Uint(_size) => {
                    let bit_repr = self.bit_representation().unwrap();
                    bit_repr.cast(builtin)
                }
                Builtin::Int(size) => {
                    // no op
                    if r_size == size {
                        Some(self)
                    } else {
                        let mask = if size == 256 {
                            U256::MAX / 2
                        } else {
                            U256::from(2).pow((size - 1).into()) - 1
                        };

                        let (_sign, abs) = val.into_sign_and_abs();

                        if abs < mask {
                            Some(Concrete::Int(size, val))
                        } else {
                            // check if the top bit for the new value is set on the existing value
                            // if it is, then the cast will result in a negative number
                            let top_mask =
                                if abs & (U256::from(1) << U256::from(size)) != U256::zero() {
                                    // sign extension
                                    ((U256::from(1) << U256::from(257 - size)) - U256::from(1))
                                        << U256::from(size - 1)
                                } else {
                                    U256::from(0)
                                };

                            Some(Concrete::Int(size, I256::from_raw((abs & mask) | top_mask)))
                        }
                    }
                }
                Builtin::Bytes(size) => {
                    let mask = if size == 32 {
                        U256::MAX
                    } else {
                        U256::from(2).pow((size as u16 * 8).into()) - 1
                    };
                    let mut h = H256::default();
                    (val.into_raw() & mask).to_big_endian(h.as_mut());
                    Some(Concrete::Bytes(size, h))
                }
                Builtin::Bool => {
                    if val.abs() > I256::from(0i32) {
                        Some(Concrete::from(true))
                    } else {
                        Some(Concrete::from(false))
                    }
                }
                _ => None,
            },
            Concrete::Bytes(cap, b) => match builtin {
                Builtin::Address => Some(Concrete::Address(Address::from_slice(&b[12..]))),
                Builtin::Uint(size) => {
                    let mask = if size == 256 {
                        U256::MAX
                    } else {
                        U256::from(2).pow(size.into()) - 1
                    };
                    let val = U256::from_big_endian(b.as_bytes());
                    Some(Concrete::Uint(size, val & mask))
                }
                Builtin::Int(size) => {
                    let mask = if size == 256 {
                        U256::MAX
                    } else {
                        U256::from(2).pow(size.into()) - 1
                    };
                    let val = U256::from_big_endian(b.as_bytes());
                    Some(Concrete::Int(size, I256::from_raw(val & mask)))
                }
                Builtin::Bytes(size) => {
                    let mut h = H256::default();
                    (0..size).for_each(|i| h.0[i as usize] = b.0[i as usize]);
                    Some(Concrete::Bytes(size, h))
                }
                Builtin::DynamicBytes => {
                    let mut bytes = vec![0; cap.into()];
                    b.0.into_iter()
                        .take(cap.into())
                        .enumerate()
                        .for_each(|(i, b)| bytes[i] = b);
                    Some(Concrete::DynBytes(bytes))
                }
                _ => None,
            },
            Concrete::Address(a) => match builtin {
                Builtin::Address => Some(self),
                Builtin::Uint(size) => {
                    let mask = if size == 256 {
                        U256::MAX
                    } else {
                        U256::from(2).pow(size.into()) - 1
                    };
                    let val = U256::from_big_endian(a.as_bytes());
                    Some(Concrete::Uint(size, val & mask))
                }
                Builtin::Int(size) => {
                    let mask = if size == 256 {
                        U256::MAX
                    } else {
                        U256::from(2).pow(size.into()) - 1
                    };
                    let val = U256::from_big_endian(a.as_bytes());
                    Some(Concrete::Int(size, I256::from_raw(val & mask)))
                }
                Builtin::Bytes(size) => {
                    let val = U256::from_big_endian(a.as_bytes());
                    let mask = if size == 32 {
                        U256::MAX
                    } else {
                        U256::from(2).pow((size as u16 * 8).into()) - 1
                    };

                    let mut h = H256::default();
                    (val & mask).to_big_endian(h.as_mut());
                    Some(Concrete::Bytes(size, h))
                }
                _ => None,
            },
            Concrete::String(s) => match builtin {
                Builtin::Bytes(size) => {
                    let as_bytes = s.as_bytes();
                    if as_bytes.len() <= size.into() {
                        let mut h = H256::default();
                        as_bytes.iter().enumerate().for_each(|(i, byte)| {
                            h.0[i] = *byte;
                        });
                        Some(Concrete::Bytes(size, h))
                    } else {
                        None
                    }
                }
                Builtin::DynamicBytes => Some(Concrete::DynBytes(s.as_bytes().to_vec())),
                _ => None,
            },
            Concrete::DynBytes(ref b) => match builtin {
                Builtin::Bytes(size) => {
                    if b.len() <= size.into() {
                        let mut h = H256::default();
                        b.iter().enumerate().for_each(|(i, byte)| {
                            h.0[i] = *byte;
                        });
                        Some(Concrete::Bytes(size, h))
                    } else {
                        None
                    }
                }
                Builtin::DynamicBytes => Some(self),
                Builtin::String => todo!(),
                _ => None,
            },
            Concrete::Bool(ref b) => match builtin {
                Builtin::Bool => Some(self),
                Builtin::Uint(_) => {
                    if *b {
                        Some(Concrete::from(U256::from(1)))
                    } else {
                        Some(Concrete::from(U256::zero()))
                    }
                }
                Builtin::Int(_) => {
                    if *b {
                        Some(Concrete::from(I256::from(1i32)))
                    } else {
                        Some(Concrete::from(I256::zero()))
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Converts a concrete into a [`Builtin`].
    pub fn as_builtin(&self) -> Builtin {
        match self {
            Concrete::Uint(size, _) => Builtin::Uint(*size),
            Concrete::Int(size, _) => Builtin::Int(*size),
            Concrete::Bytes(size, _) => Builtin::Bytes(*size),
            Concrete::Address(_) => Builtin::Address,
            Concrete::Bool(_b) => Builtin::Bool,
            Concrete::DynBytes(_) => Builtin::DynamicBytes,
            Concrete::String(_) => Builtin::String,
            _ => panic!("uncastable to builtin"),
        }
    }

    /// Converts a concrete into a `U256`.
    pub fn into_u256(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            Concrete::Int(_, val) => {
                if val >= &I256::from(0) {
                    Some(val.into_raw())
                } else {
                    None
                }
            }
            Concrete::Bytes(_, b) => Some(U256::from_big_endian(b.as_bytes())),
            Concrete::DynBytes(v) if v.len() <= 32 => {
                self.clone().cast(Builtin::Bytes(v.len() as u8))?.into_u256()
            },
            Concrete::Address(a) => Some(U256::from_big_endian(a.as_bytes())),
            Concrete::Bool(b) => {
                if *b {
                    Some(1.into())
                } else {
                    Some(0.into())
                }
            }
            _ => None,
        }
    }

    /// Returns this concrete as a max-sized version
    pub fn max_size(&self) -> Self {
        match self {
            Concrete::Uint(_, val) => Concrete::Uint(256, *val),
            Concrete::Int(_, val) => Concrete::Int(256, *val),
            Concrete::Bytes(_, val) => Concrete::Bytes(32, *val),
            _ => self.clone(),
        }
    }

    /// Gets the default max for a given concrete variant.
    pub fn max(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => {
                let max = if *size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(*size)) - 1
                };
                Some(Concrete::Uint(*size, max))
            }
            Concrete::Int(size, _) => {
                let max: I256 =
                    I256::from_raw((U256::from(1u8) << U256::from(*size - 1)) - U256::from(1));
                Some(Concrete::Int(*size, max))
            }
            Concrete::Bytes(size, _) => {
                let size = *size as u16 * 8;
                let max = if size == 256 {
                    U256::MAX
                } else {
                    U256::from(2).pow(U256::from(size)) - 1
                };

                let mut h = H256::default();
                max.to_big_endian(h.as_mut());
                Some(Concrete::Bytes((size / 8) as u8, h))
            }
            Concrete::Address(_) => Some(Concrete::Address(Address::from_slice(&[0xff; 20]))),
            Concrete::Bool(_) => Some(Concrete::Bool(true)),
            _ => None,
        }
    }

    pub fn possible_builtins_from_ty_inf(&self) -> Vec<Builtin> {
        let mut builtins = vec![];
        match self {
            Concrete::Uint(_size, val) => {
                let mut min_bits = (256 - val.leading_zeros()) as u16;
                let mut s = 256;
                while s > min_bits {
                    builtins.push(Builtin::Uint(s));
                    s -= 8;
                }
                // now ints
                min_bits = min_bits.saturating_sub(1);
                let mut s = 255;
                while s > min_bits {
                    builtins.push(Builtin::Int(s + 1));
                    s = s.saturating_sub(8);
                }
            }
            Concrete::Int(size, val) => {
                // if we evaled it as a int, it must be negative
                let (abs, is_min) = val.overflowing_abs();
                if is_min {
                    builtins.push(Builtin::Int(*size))
                } else {
                    let min_bits = (255 - abs.leading_zeros()) as u16;
                    let mut s = *size;
                    while s > min_bits {
                        builtins.push(Builtin::Int(s));
                        s -= 8;
                    }
                }
            }
            Concrete::Bytes(size, val) => {
                let min_bytes: u8 =
                    val.as_fixed_bytes()
                        .iter()
                        .rev()
                        .enumerate()
                        .fold(0, |mut acc, (i, v)| {
                            if v != &0x00u8 {
                                acc = i as u8;
                                acc
                            } else {
                                acc
                            }
                        });
                let mut s = *size;
                while s > min_bytes {
                    builtins.push(Builtin::Bytes(s));
                    s -= 1;
                }
            }
            _ => {}
        }
        builtins
    }

    /// Gets the smallest increment for a given type
    pub fn one(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => Some(Concrete::Uint(*size, U256::from(1))),
            Concrete::Int(size, _) => Some(Concrete::Int(*size, I256::from(1))),
            Concrete::Bytes(size, _) => {
                let mut b = [0x00; 32];
                b[0] = 0x01;
                Some(Concrete::Bytes(size / 8, H256::from(b)))
            }
            Concrete::Address(_) => {
                let mut b = [0x00; 20];
                b[19] = 0x01;
                Some(Concrete::Address(Address::from_slice(&b)))
            }
            Concrete::Bool(_) => Some(Concrete::Bool(true)),
            _ => None,
        }
    }

    /// Gets the default min for a given concrete variant.
    pub fn min(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => Some(Concrete::Uint(*size, 0.into())),
            Concrete::Int(size, _) => {
                let max = if size == &256u16 {
                    I256::MAX
                } else {
                    I256::from_raw(U256::from(1u8) << U256::from(*size - 1)) - I256::from(1)
                };

                let min = max * I256::from(-1i32) - I256::from(1i32);
                Some(Concrete::Int(*size, min))
            }
            Concrete::Bytes(size, _) => {
                let min = U256::zero();
                let mut h = H256::default();
                min.to_big_endian(h.as_mut());
                Some(Concrete::Bytes(*size, h))
            }
            Concrete::Address(_) => Some(Concrete::Address(Address::from_slice(&[0x00; 20]))),
            Concrete::Bool(_) => Some(Concrete::Bool(false)),
            Concrete::String(_) => Some(Concrete::String("".to_string())),
            Concrete::DynBytes(_) => Some(Concrete::DynBytes(vec![])),
            Concrete::Array(_) => Some(Concrete::Array(vec![])),
        }
    }

    /// Gets the size of some concrete type
    pub fn int_size(&self) -> Option<u16> {
        match self {
            Concrete::Uint(size, _) => Some(*size),
            Concrete::Int(size, _) => Some(*size),
            Concrete::Bytes(size, _) => Some(*size as u16),
            _ => None,
        }
    }

    /// If its `Concrete::Uint`, gets the value
    pub fn uint_val(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            _ => None,
        }
    }

    /// If its `Concrete::Int`, gets the value
    pub fn int_val(&self) -> Option<I256> {
        match self {
            Concrete::Int(_, val) => Some(*val),
            _ => None,
        }
    }

    pub fn as_hex_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => {
                let mut bytes = [0u8; 32];
                val.to_big_endian(&mut bytes);
                format!("0x{}", hex::encode(bytes))
            },
            Concrete::Int(_, val) => {
                let mut bytes = [0u8; 32];
                val.to_big_endian(&mut bytes);
                format!("0x{}", hex::encode(bytes))
            },
            Concrete::Bytes(size, b) => format!(
                "0x{}",
                b.0.iter()
                    .take(*size as usize)
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<Vec<_>>()
                    .join("")
            ),
            Concrete::String(s) => hex::encode(s),
            Concrete::Bool(_b) => self.bit_representation().unwrap().as_hex_string(),
            Concrete::Address(_a) => self.bit_representation().unwrap().as_hex_string(),
            Concrete::DynBytes(a) => {
                if a.is_empty() {
                    "0x".to_string()
                } else {
                    hex::encode(a)
                }
            }
            Concrete::Array(arr) => format!(
                "0x{}",
                arr.iter()
                    .map(|i| i.as_hex_string()[2..].to_string())
                    .collect::<Vec<String>>()
                    .join("")
            ),
        }
    }
    /// Converts to a string
    pub fn as_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => val.to_string(),
            Concrete::Int(_, val) => val.to_string(),
            Concrete::Bytes(size, b) => format!(
                "0x{}",
                b.0.iter()
                    .take(*size as usize)
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<Vec<_>>()
                    .join("")
            ),
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => a.to_string(),
            Concrete::DynBytes(a) => {
                if a.is_empty() {
                    "0x".to_string()
                } else {
                    hex::encode(a)
                }
            }
            Concrete::Array(arr) => format!(
                "[{}]",
                arr.iter()
                    .map(|i| i.as_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }

    /// Converts to a human readable string. For integers, this means trying to find a
    /// power of 2 that is close to the value.
    pub fn as_human_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => {
                let cutoff = U256::from(2).pow(U256::from(32));
                if val < &cutoff {
                    val.to_string()
                } else {
                    for size in 32..=255 {
                        let pow2 = U256::from(2).pow(U256::from(size));
                        if val < &pow2 {
                            let diff = pow2 - val;
                            if diff < cutoff {
                                return format!("2**{size} - {diff}");
                            }
                        } else if *val == pow2 {
                            return format!("2**{size}");
                        } else {
                            let diff = val - pow2;
                            if diff < cutoff {
                                return format!("2**{size} + {diff}");
                            }
                        }
                    }

                    let pow2 = U256::MAX;
                    if val < &pow2 {
                        let diff = pow2 - val;
                        if diff < cutoff {
                            return format!("2**{} - {}", 256, diff + 1);
                        }
                    } else if *val == pow2 {
                        return format!("2**{} - 1", 256);
                    }

                    val.to_string()
                }
            }
            Concrete::Int(size, val) => {
                let cutoff = I256::from(2).pow(32);
                if val < &cutoff && val > &(I256::from(-1i32) * cutoff) {
                    return val.to_string();
                }

                if val > &I256::from(0) {
                    let val = val.into_sign_and_abs().1;
                    Concrete::Uint(*size, val).as_human_string()
                } else {
                    let val = val.into_sign_and_abs().1;
                    format!("-1 * {}", Concrete::Uint(*size, val).as_human_string())
                }
            }
            Concrete::Bytes(size, b) => {
                format!(
                    "0x{}",
                    b.0.iter()
                        .take(*size as usize)
                        .map(|byte| format!("{byte:02x}"))
                        .collect::<Vec<_>>()
                        .join("")
                )
            }
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => format!("{a:?}"),
            Concrete::DynBytes(a) => {
                if a.is_empty() {
                    "0x".to_string()
                } else {
                    hex::encode(a)
                }
            }
            Concrete::Array(arr) => format!(
                "[{}]",
                arr.iter()
                    .map(|i| i.as_human_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}
