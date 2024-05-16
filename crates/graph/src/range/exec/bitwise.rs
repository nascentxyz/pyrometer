use crate::nodes::Concrete;
use crate::range::{elem::*, exec_traits::*};
use ethers_core::types::{H256, U256};

impl RangeBitwise<Concrete> for RangeConcrete<Concrete> {
    fn range_bit_and(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a & *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Uint(s, u), Concrete::Int(s2, i))
            | (Concrete::Int(s, i), Concrete::Uint(s2, u)) => {
                let op_res = *u & i.into_raw();
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a & b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l & r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
        }
    }

    fn range_bit_or(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a | *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a | b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l | r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
        }
    }

    fn range_bit_xor(&self, other: &Self) -> Option<Elem<Concrete>> {
        match (&self.val, &other.val) {
            (Concrete::Uint(s, a), Concrete::Uint(s2, b)) => {
                let op_res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Uint(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Int(s, a), Concrete::Int(s2, b)) => {
                let op_res = *a ^ *b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Int(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            (Concrete::Bytes(s, a), Concrete::Bytes(s2, b)) => {
                let op_res = a ^ b;
                let size = if s > s2 { s } else { s2 };
                let val = Concrete::Bytes(*size, op_res);
                let rc = RangeConcrete::new(val, self.loc);
                Some(rc.into())
            }
            _ => {
                if let (Some(l), Some(r)) = (self.val.into_u256(), other.val.into_u256()) {
                    let op_res = l ^ r;
                    let val = self.val.u256_as_original(op_res);
                    let rc = RangeConcrete::new(val, self.loc);
                    Some(rc.into())
                } else {
                    None
                }
            }
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
                let op_res = val & max;
                let rc = RangeConcrete::new(Concrete::Uint(*size, op_res), self.loc);
                Some(rc.into())
            }
            Concrete::Int(size, a) => {
                let (op_res, _) = a.overflowing_neg();
                let (op_res, _) = op_res.overflowing_sub(1.into());
                let rc = RangeConcrete::new(Concrete::Int(*size, op_res), self.loc);
                Some(rc.into())
            }
            Concrete::Bytes(s, a) => {
                let mut op_res = H256::default();
                (0..*s).for_each(|i| {
                    op_res.0[i as usize] = !a.0[i as usize];
                });
                let rc = RangeConcrete::new(Concrete::Bytes(*s, op_res), self.loc);
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

#[cfg(test)]
mod tests {
    use super::*;
    use ethers_core::types::{I256, U256};
    use solang_parser::pt::Loc;

    #[test]
    fn and_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(5)));
    }

    #[test]
    fn and_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-15)));
    }

    #[test]
    fn and_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_and(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::from(h2));
    }

    #[test]
    fn or_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(15)));
    }

    #[test]
    fn or_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(-5)));
    }

    #[test]
    fn or_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_or(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::from(h));
    }

    #[test]
    fn xor_uint_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Uint(256, U256::from(5)), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::from(10)));
    }

    #[test]
    fn xor_int_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::Int(256, I256::from(-5i32)), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(10)));
    }

    #[test]
    fn xor_bytes_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1, 1, 1, 1][..]);
        let mut h2: [u8; 32] = [0; 32];
        h2[0..4].copy_from_slice(&[0, 1, 0, 1][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let y = RangeConcrete::new(Concrete::from(h2), Loc::Implicit);
        let result = x.range_bit_xor(&y).unwrap().maybe_concrete_value().unwrap();

        let mut expected: [u8; 32] = [0; 32];
        expected[0..3].copy_from_slice(&[1, 0, 1][..]);
        assert_eq!(result.val, Concrete::from(expected));
    }

    #[test]
    fn not_uint() {
        let x = RangeConcrete::new(Concrete::Uint(256, U256::from(15)), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Uint(256, U256::MAX << 4));
    }

    #[test]
    fn not_int() {
        let x = RangeConcrete::new(Concrete::Int(256, I256::from(-15i32)), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();
        assert_eq!(result.val, Concrete::Int(256, I256::from(14)));
    }

    #[test]
    fn not_bytes() {
        let mut h: [u8; 32] = [0; 32];
        h[0..4].copy_from_slice(&[1; 4][..]);
        let x = RangeConcrete::new(Concrete::from(h), Loc::Implicit);
        let result = x.range_bit_not().unwrap().maybe_concrete_value().unwrap();

        let mut expected: [u8; 32] = [255; 32];
        expected[0..4].copy_from_slice(&[254, 254, 254, 254][..]);
        assert_eq!(result.val, Concrete::from(expected));
    }
}
