use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use ethers_core::types::{H256, U256};

impl RangeBitwise<Concrete> for RangeConcrete<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Uint(s, u), Concrete::Int(s2, i))
            | (Concrete::Int(s, i), Concrete::Uint(s2, u)) => {
                let res = *u & i.into_raw();
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let res = a & b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => None,
        }
    }

    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let res = a | b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => None,
        }
    }

    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let res = a ^ b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => None,
        }
    }

    fn range_bit_not(&self) -> Option<Elem<Concrete>> {
        match &self.val {
            Concrete::Uint(size, a) => {
                let max = Concrete::max_of_type(&self.val)
                    .unwrap()
                    .uint_val()
                    .unwrap();
                let val = U256(
                    a.0.into_iter()
                        .map(|i| !i)
                        .collect::<Vec<_>>()
                        .try_into()
                        .unwrap(),
                );
                let res = val & max;
                let rc = RangeConcrete::new(Concrete::Uint(*size, res), self.loc);
                Some(rc.into())
            }
            Concrete::Int(size, a) => {
                let (val, _) = a.overflowing_neg();
                let (val, _) = val.overflowing_sub(1.into());
                let rc = RangeConcrete::new(Concrete::Int(*size, val), self.loc);
                Some(rc.into())
            }
            Concrete::Bytes(s, a) => {
                let mut h = H256::default();
                (0..*s).for_each(|i| {
                    h.0[i as usize] = !a.0[i as usize];
                });
                let rc = RangeConcrete::new(Concrete::Bytes(*s, h), self.loc);
                Some(rc.into())
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
