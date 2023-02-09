use crate::Builtin;
use crate::{Node, NodeIdx, analyzer::{GraphLike}};
use ethers_core::types::{U256, I256, H256, Address};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConcreteNode(pub usize);

impl ConcreteNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphLike) -> &'a Concrete {
        match analyzer.node(*self) {
            Node::Concrete(c) => c,
            e => panic!(
                "Node type confusion: expected node to be Concrete but it was: {:?}",
                e
            ),
        }
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

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Concrete {
    Uint(u16, U256),
    Int(u16, I256),
    Bytes(u8, H256),
    Address(Address),
    Bool(bool),
    DynBytes(Vec<u8>),
    String(String),
    Array(Vec<Concrete>),
}

impl From<U256> for Concrete {
    fn from(u: U256) -> Self {
        Concrete::Uint(256, u)
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
            _ => todo!("here"),
        }
    }

    pub fn cast_from(self, other: &Self) -> Option<Self> {
        self.cast(other.as_builtin())
    }

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
                        Some(Concrete::Uint(size, val & mask))
                    }
                    Builtin::Int(size) => {
                        let mask = if size == 256 {
                            // we ignore the top bit
                            U256::from(2).pow(255.into()) - 1
                        } else {
                            U256::from(2).pow(size.into()) - 1
                        };
                        Some(Concrete::Int(size, I256::from_raw(val & mask)))
                    }
                    Builtin::Bytes(size) => {
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
                        Some(Concrete::Uint(size, val.into_raw() & mask))
                    }
                    Builtin::Int(size) => {
                        let mask = if size == 256 {
                            U256::MAX
                        } else {
                            U256::from(2).pow(size.into()) - 1
                        };
                        Some(Concrete::Int(size, I256::from_raw(val.into_raw() & mask)))
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
            Concrete::Bytes(_, b) => {
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
                        let mask = if size == 32 {
                            U256::MAX
                        } else {
                            U256::from(2).pow((size as u16 * 8).into()) - 1
                        };

                        let mut h = H256::default();
                        let val = U256::from_big_endian(b.as_bytes());
                        (val & mask).to_big_endian(h.as_mut());
                        Some(Concrete::Bytes(size, h))
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
            _ => None
        }
    }

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

    pub fn into_u256(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            Concrete::Int(_, val) => if val > &I256::from(0) { Some(val.into_raw()) } else { None },
            Concrete::Bytes(_, b) => Some(U256::from_big_endian(b.as_bytes())),
            Concrete::Address(a) => Some(U256::from_big_endian(a.as_bytes())),
            Concrete::Bool(b) => if *b { Some(1.into()) } else { Some(0.into()) },
            _ => None,
        }
    }

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
                    I256::from_raw(U256::from(1u8) << U256::from(*size - 1)) - 1.into();
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

    pub fn min(&self) -> Option<Self> {
        match self {
            Concrete::Uint(size, _) => {
                Some(Concrete::Uint(*size, 0.into()))
            },
            Concrete::Int(size, _) => {
                let max: I256 =
                    I256::from_raw(U256::from(1u8) << U256::from(*size - 1)) - 1.into();
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
            _ => None,
        }
    }

    pub fn int_size(&self) -> Option<u16> {
        match self {
            Concrete::Uint(size, _) => Some(*size),
            Concrete::Int(size, _) => Some(*size),
            Concrete::Bytes(size, _) => Some(*size as u16),
            _ => None,
        }
    }

    pub fn uint_val(&self) -> Option<U256> {
        match self {
            Concrete::Uint(_, val) => Some(*val),
            _ => None,
        }
    }

    pub fn int_val(&self) -> Option<I256> {
        match self {
            Concrete::Int(_, val) => Some(*val),
            _ => None,
        }
    }

    pub fn as_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => val.to_string(),
            Concrete::Int(_, val) => val.to_string(),
            Concrete::Bytes(_, b) => format!("0x{:x}", b),
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => a.to_string(),
            _ => todo!("concrete as string"),
        }
    }

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
            Concrete::Bytes(_, b) => format!("0x{:x}", b),
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            Concrete::Address(a) => format!("{:?}", a),
            _ => todo!("concrete as string"),
        }
    }
}
