use crate::{Node, NodeIdx, analyzer::AnalyzerLike};
use ethers_core::types::{U256, I256, H256, Address};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct ConcreteNode(pub usize);

impl ConcreteNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl AnalyzerLike) -> &'a Concrete {
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

impl Into<NodeIdx> for ConcreteNode {
    fn into(self) -> NodeIdx {
        self.0.into()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Concrete {
    Uint(u16, U256),
    Int(u16, I256),
    Bytes(u8, H256),
    Address(Address),
    DynBytes(Vec<u8>),
    String(String),
    Bool(bool),
    Array(Vec<Concrete>),
}
impl From<U256> for Concrete {
    fn from(u: U256) -> Self {
        Concrete::Uint(256, u)
    }
}

impl Concrete {
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
            _ => todo!("concrete as string"),
        }
    }

    pub fn as_human_string(&self) -> String {
        match self {
            Concrete::Uint(_, val) => {
                let cutoff = U256::from(2).pow(U256::from(32));
                if val < &cutoff {
                    return val.to_string();
                } else {
                    for i in 4..32 {
                        let size = i*8;
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
            Concrete::Int(_, val) => val.to_string(),
            Concrete::Bytes(_, b) => format!("0x{:x}", b),
            Concrete::String(s) => s.to_string(),
            Concrete::Bool(b) => b.to_string(),
            _ => todo!("concrete as string"),
        }
    }
}
