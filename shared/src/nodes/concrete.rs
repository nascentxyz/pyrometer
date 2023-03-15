use crate::Builtin;
use crate::{Node, NodeIdx, analyzer::{GraphLike}};
use ethers_core::types::{U256, I256, H256, Address};

/// An index in the graph that references a [`Concrete`] node
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConcreteNode(pub usize);

impl ConcreteNode {
    /// Gets the underlying node data for the [`Concrete`]
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Concrete {
        match analyzer.node(*self) {
            Node::Concrete(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Concrete but it was: {:?}",
                e
            ),
        }
    }

    pub fn max_size(&self, analyzer: &mut impl GraphLike) -> Self {
        let c = self.underlying(analyzer).max_size();
        analyzer.add_node(Node::Concrete(c)).into()
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

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum DynCapacity {
    Cap(U256),
    Unlimited,
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
    /// A (capacity, vector of bytes)
    DynBytes(Vec<u8>),
    /// A string, (TODO: solidity doesn't enforce utf-8 encoding like rust. Likely this type
    /// should be modeled with a `Vec<u8>` instead.)
    String(String),
    /// An array of concrete values
    Array(Vec<Concrete>),
}

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
    /// Convert a U256 back into it's original type. This is used mostly
    /// for range calculations to improve ergonomics. Basically
    /// the EVM only operates on U256 words, so most of this should
    /// be fine.
    pub fn u256_as_original(&self, uint: U256) -> Self {
        match self {
            Concrete::Uint(size, _) => Concrete::Uint(*size, uint),
            Concrete::Int(size, _) => Concrete::Int(*size, I256::from_raw(uint)),
            Concrete::Bytes(size, _) => {
                let mut h = H256::default();
                uint.to_big_endian(h.as_mut());
                Concrete::Bytes(*size, h)
            },
            Concrete::Address(_) => {
                let mut bytes = [0u8; 32];
                uint.to_big_endian(&mut bytes);
                Concrete::Address(Address::from_slice(&bytes[12..]))
            },
            Concrete::Bool(_) => if uint > U256::zero() { Concrete::Bool(true) } else { Concrete::Bool(false) },
            e => todo!("Unsupported: {e:?}"),
        }
    }

    /// Cast from one concrete variant given another concrete variant
    pub fn cast_from(self, other: &Self) -> Option<Self> {
        self.cast(other.as_builtin())
    }

    pub fn equivalent_ty(&self, other: &Self) -> bool {
        match (self, other) {
            (Concrete::Uint(size, _), Concrete::Uint(other_size, _)) if size == other_size => true,
            (Concrete::Int(size, _), Concrete::Int(other_size, _)) if size == other_size => true,
            (Concrete::Bytes(size, _), Concrete::Bytes(other_size, _)) if size == other_size => true,
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
            _ => false
        }
    }

    pub fn is_int(&self) -> bool {
        matches!(self, Concrete::Int(_, _))
    }

    /// Cast the concrete to another type as denoted by a [`Builtin`].
    pub fn cast(self, builtin: Builtin) -> Option<Self> {
        match self {
            Concrete::Uint(_, val) => {
                match builtin {
                    Builtin::Address => {
                        let mut bytes = [0u8; 32];
                        val.to_big_endian(&mut bytes);
                        Some(Concrete::Address(Address::from_slice(&bytes[12..])))
                    }
                    Builtin::Uint(size) => {
                        let mask = if size == 256 {
                            U256::MAX
                        } else {
                            U256::from(2).pow(size.into()) - 1
                        };
                        if val < mask {
                            Some(Concrete::Uint(size, val))    
                        } else {
                            Some(Concrete::Uint(size, mask))
                        }
                    }
                    Builtin::Int(size) => {
                        let mask = if size == 256 {
                            // we ignore the top bit
                            U256::from(2).pow(255.into()) - 1
                        } else {
                            U256::from(2).pow(size.into()) - 1
                        };

                        if val < mask {
                            Some(Concrete::Int(size, I256::from_raw(val)))
                        } else {
                            Some(Concrete::Int(size, I256::from_raw(mask)))
                        }
                    }
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
                    _ => None
                }
            }
            Concrete::Int(_, val) => {
                match builtin {
                    Builtin::Address => {
                        let mut bytes = [0u8; 32];
                        val.to_big_endian(&mut bytes);
                        Some(Concrete::Address(Address::from_slice(&bytes[12..])))
                    }
                    Builtin::Uint(size) => {
                        let mask = if size == 256 {
                            U256::MAX
                        } else {
                            U256::from(2).pow(size.into()) - 1
                        };

                        let (_sign, abs) = val.into_sign_and_abs();

                        if val.signum() <= 0.into() {
                            Some(Concrete::Uint(size, U256::zero()))
                        } else if abs < mask {
                            Some(Concrete::Uint(size, abs))
                        } else {
                            Some(Concrete::Uint(size, mask))
                        }
                    }
                    Builtin::Int(size) => {
                        let mask = if size == 256 {
                            U256::MAX / 2
                        } else {
                            U256::from(2).pow((size - 1).into()) - 1
                        };

                        let (sign, abs) = val.into_sign_and_abs();
                        if abs < mask {
                            Some(Concrete::Int(size, val))
                        } else {
                            Some(Concrete::Int(size, I256::checked_from_sign_and_abs(sign, mask).unwrap())) 
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
                    _ => None
                }
            }
            Concrete::Bytes(cap, b) => {
                match builtin {
                    Builtin::Address => {
                        Some(Concrete::Address(Address::from_slice(&b[12..])))
                    }
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
                        b.0.into_iter().take(cap.into()).enumerate().for_each(|(i, b)| bytes[i] = b);
                        Some(Concrete::DynBytes(bytes))
                    }
                    _ => None
                }
            }
            Concrete::Address(a) => {
                match builtin {
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
                    _ => None
                }
            }
            Concrete::DynBytes(ref _b) => {
                match builtin {
                    Builtin::DynamicBytes => Some(self),
                    Builtin::String => todo!(),
                    _ => None
                }
            }
            _ => None
        }
    }

    /// Converts a concrete into a [`Builtin`].
    pub fn as_builtin(&self) -> Builtin {
        match self {
            Concrete::Uint(size, _) => {
                Builtin::Uint(*size)
            }
            Concrete::Int(size, _) => {
                Builtin::Int(*size)
            }
            Concrete::Bytes(size, _) => {
                Builtin::Bytes(*size)
            }
            Concrete::Address(_) => {
                Builtin::Address
            }
            Concrete::Bool(_b) => {
                Builtin::Bool
            }
            Concrete::DynBytes(_) => Builtin::DynamicBytes,
            Concrete::String(_) => Builtin::String,
            _ => panic!("uncastable to builtin"),
        }
    }

    /// Converts a concrete into a `U256`.
    pub fn into_u256(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            Concrete::Int(_, val) => if val >= &I256::from(0) { Some(val.into_raw()) } else { None },
            Concrete::Bytes(_, b) => Some(U256::from_big_endian(b.as_bytes())),
            Concrete::Address(a) => Some(U256::from_big_endian(a.as_bytes())),
            Concrete::Bool(b) => if *b { Some(1.into()) } else { Some(0.into()) },
            _ => None,
        }
    }

    pub fn max_size(&self) -> Self {
        match self {
            Concrete::Uint(_, val) => {
                Concrete::Uint(256, *val)
            },
            Concrete::Int(_, val) => {
                Concrete::Int(256, *val)
            },
            Concrete::Bytes(_, val) => {
                Concrete::Bytes(32, *val)
            },
            _ => self.clone()
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
            },
            Concrete::Int(size, _) => {
                let max: I256 =
                    I256::from_raw((U256::from(1u8) << U256::from(*size - 1)) - U256::from(1));
                Some(Concrete::Int(*size, max))
            },
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
            },
            Concrete::Address(_) => {
                Some(Concrete::Address(Address::from_slice(&[0xff; 20])))
            },
            _ => None,
        }
    }

    pub fn possible_builtins_from_ty_inf(&self) -> Vec<Builtin> {
        let mut builtins = vec![];
        match self {
            Concrete::Uint(size, val) => {
                let mut min_bits = (256 - val.leading_zeros()) as u16;
                let mut s = *size;
                while s > min_bits {
                    builtins.push(Builtin::Uint(s));
                    s -= 8;
                }
                // now ints
                min_bits = min_bits.saturating_sub(1);
                let mut s = *size;
                while s > min_bits {
                    builtins.push(Builtin::Int(s));
                    s -= 8;
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
                let min_bytes: u8 = val.as_fixed_bytes().iter().rev().enumerate().fold(0, |mut acc, (i, v)| {
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
            _ => {},
        }
        builtins
    }

    /// Gets the smallest increment for a given type
    pub fn one(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => {
                Some(Concrete::Uint(*size, U256::from(1)))
            },
            Concrete::Int(size, _) => {
                Some(Concrete::Int(*size, I256::from(1)))
            },
            Concrete::Bytes(size, _) => {
                let mut b = [0x00; 32];
                b[0] = 0x01;
                Some(Concrete::Bytes(size / 8, H256::from(b)))
            },
            Concrete::Address(_) => {
                let mut b = [0x00; 20];
                b[19] = 0x01;
                Some(Concrete::Address(Address::from_slice(&b)))
            },
            _ => None,
        }
    }

    /// Gets the default min for a given concrete variant.
    pub fn min(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => {
                Some(Concrete::Uint(*size, 0.into()))
            },
            Concrete::Int(size, _) => {
                let max = if size == &256u16 {
                    I256::MAX
                } else {
                    I256::from_raw(U256::from(1u8) << U256::from(*size - 1)) - I256::from(1)
                };

                let min = max * I256::from(-1i32);
                Some(Concrete::Int(*size, min))
            },
            Concrete::Bytes(size, _) => {
                let min = U256::zero();
                let mut h = H256::default();
                min.to_big_endian(h.as_mut());
                Some(Concrete::Bytes(*size, h))
            },
            Concrete::Address(_) => {
                Some(Concrete::Address(Address::from_slice(&[0x00; 20])))
            },
            e => { println!("was other: {e:?}"); None},
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

    /// Converts to a string
    pub fn as_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => val.to_string(),
            Concrete::Int(_, val) => val.to_string(),
            Concrete::Bytes(size, b) => format!("0x{}", b.0.iter().take(*size as usize).map(|byte| format!("{:02x}", byte)).collect::<Vec<_>>().join("")),
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => a.to_string(),
            Concrete::DynBytes(a) => if a.is_empty() { "0x".to_string() } else { hex::encode(a) },
            e => todo!("Concrete as string {e:?}"),
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
                                return format!("2**{} - {}", size, diff);
                            }
                        } else if *val == pow2 {
                            return format!("2**{}", size);
                        } else {
                            let diff = val - pow2;
                            if diff < cutoff {
                                return format!("2**{} + {}", size, diff);
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
            },
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
            },
            Concrete::Bytes(size, b) => {
                format!("0x{}", b.0.iter().take(*size as usize).map(|byte| format!("{:02x}", byte)).collect::<Vec<_>>().join(""))
            },
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => format!("{:?}", a),
            Concrete::DynBytes(a) => if a.is_empty() { "0x".to_string() } else { hex::encode(a) },
            e => todo!("Concrete as string: {e:?}"),
        }
    }
}
