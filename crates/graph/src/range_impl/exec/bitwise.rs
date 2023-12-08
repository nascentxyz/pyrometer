use crate::nodes::Concrete;
use range::{elem::*, exec::*};
use ethers_core::types::{H256, U256};

impl RangeBitwise<Concrete> for RangeConcrete<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a & *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a & *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Uint(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a & b.into_raw()),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, a.into_raw() & *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(*size, a & b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }

    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a | *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a | *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(*size, a | b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }

    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, *a ^ *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, *a ^ *b),
                    loc: self.loc,
                }))
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let size = if s > s2 { s } else { s2 };
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(*size, a ^ b),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }

    fn range_bit_not(&self) -> Option<Elem<Concrete>> {
        match &self.val {
            Concrete::Uint(size, a) => {
                let max = Concrete::max(&self.val).unwrap().uint_val().unwrap();
                let val = U256(
                    a.0.into_iter()
                        .map(|i| !i)
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                );
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Uint(*size, val & max),
                    loc: self.loc,
                }))
            }
            Concrete::Int(size, a) => {
                let (val, _) = a.overflowing_neg();
                let (val, _) = val.overflowing_sub(1.into());
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Int(*size, val),
                    loc: self.loc,
                }))
            }
            Concrete::Bytes(s, a) => {
                let mut h = H256::default();
                (0..*s).for_each(|i| {
                    h.0[i as usize] = !a.0[i as usize];
                });
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bytes(*s, h),
                    loc: self.loc,
                }))
            }
            _ => None,
        }
    }
}

impl RangeBitwise<Concrete> for Elem<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_and(b),
            _ => None,
        }
    }
    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_or(b),
            _ => None,
        }
    }
    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (self, other) {
            (Elem::Concrete(a), Elem::Concrete(b)) => a.range_bit_xor(b),
            _ => None,
        }
    }

    fn range_bit_not(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(a) => a.range_bit_not(),
            _ => None,
        }
    }
}