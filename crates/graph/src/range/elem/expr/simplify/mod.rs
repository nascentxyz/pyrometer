mod add;
mod ords;
mod sub;

pub use add::*;
pub use ords::*;
pub use sub::*;

use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeElem, RangeOp},
};

use ethers_core::types::U256;
use shared::RangeArena;

pub(crate) fn ident_rules(
    l: &Elem<Concrete>,
    exec_op: RangeOp,
    r: &Elem<Concrete>,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let zero = Elem::from(Concrete::from(U256::zero()));
    let one = Elem::from(Concrete::from(U256::one()));
    match exec_op {
        RangeOp::Add(_) | RangeOp::Sub(_) => {
            let lhs_zero = matches!(l.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal));
            let rhs_zero = matches!(r.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal));
            match (lhs_zero, rhs_zero) {
                (true, true) => Some(Elem::from(Concrete::from(U256::zero()))),
                (true, false) => Some((*r).clone()),
                (false, true) => Some((*l).clone()),
                _ => None,
            }
        }
        RangeOp::Mul(_) | RangeOp::Div(_) => {
            let lhs_one = matches!(l.range_ord(&one, arena), Some(std::cmp::Ordering::Equal));
            let rhs_one = matches!(r.range_ord(&one, arena), Some(std::cmp::Ordering::Equal));
            match (lhs_one, rhs_one) {
                (true, true) => Some(Elem::from(Concrete::from(U256::one()))),
                (true, false) => Some((*r).clone()),
                (false, true) => Some((*l).clone()),
                _ => None,
            }
        }
        RangeOp::Exp => {
            if matches!(r.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal)) {
                Some(Elem::from(Concrete::from(U256::one())))
            } else {
                None
            }
        }
        _ => None,
    }
}
