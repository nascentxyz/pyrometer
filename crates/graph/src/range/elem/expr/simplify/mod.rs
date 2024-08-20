mod add;
mod div;
mod ords;
mod sub;

pub use add::*;
pub use ords::*;
pub use sub::*;

use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeElem, RangeOp},
};

use alloy_primitives::U256;
use shared::RangeArena;

pub(crate) fn ident_rules(
    l: &Elem<Concrete>,
    exec_op: RangeOp,
    r: &Elem<Concrete>,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    let zero = Elem::from(Concrete::from(U256::ZERO));
    let one = Elem::from(Concrete::from(U256::from(1)));
    match exec_op {
        RangeOp::Add(_) | RangeOp::Sub(_) => {
            // <x|0> + <y|0> = <x|y>
            let lhs_zero = matches!(l.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal));
            let rhs_zero = matches!(r.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal));
            match (lhs_zero, rhs_zero) {
                (true, true) => Some(Elem::from(Concrete::from(U256::ZERO))),
                (true, false) => Some((*r).clone()),
                (false, true) => Some((*l).clone()),
                _ => None,
            }
        }
        RangeOp::Div(_) => {
            let l_ord_zero = l.range_ord(&zero, arena);
            if matches!(l_ord_zero, Some(std::cmp::Ordering::Equal)) {
                // 0 / <y> = 0
                return Some(zero);
            }

            let r_ord_one = r.range_ord(&one, arena);
            if matches!(r_ord_one, Some(std::cmp::Ordering::Equal)) {
                // <x> / <1> = x
                // rhs == 1
                return Some((*l).clone());
            }

            let r_ord_l = r.range_ord(l, arena);
            let r_ord_zero = r.range_ord(&zero, arena);
            if r_ord_zero == l_ord_zero {
                match r_ord_zero {
                    Some(std::cmp::Ordering::Less) => {
                        if matches!(r_ord_l, Some(std::cmp::Ordering::Less)) {
                            // <x> / <y> = 0 if y < x && y.sign < 0 && x.sign < 0
                            return Some(zero);
                        }
                    }
                    Some(std::cmp::Ordering::Greater) => {
                        if matches!(r_ord_l, Some(std::cmp::Ordering::Greater)) {
                            // <x> / <y> = 0 if y > x && y.sign >= 0 && x.sign >= 0
                            return Some(zero);
                        }
                    }
                    _ => {}
                }
            }

            if matches!(r.range_ord(l, arena), Some(std::cmp::Ordering::Equal)) {
                // <x> / <x> = 1
                // rhs == lhs, its a one
                return Some(one);
            }

            None
        }
        RangeOp::Mul(_) => {
            // <x|1> + <y|1> = <x|y>
            let lhs_one = matches!(l.range_ord(&one, arena), Some(std::cmp::Ordering::Equal));
            let rhs_one = matches!(r.range_ord(&one, arena), Some(std::cmp::Ordering::Equal));
            match (lhs_one, rhs_one) {
                (true, true) => Some(Elem::from(Concrete::from(U256::from(1)))),
                (true, false) => Some((*r).clone()),
                (false, true) => Some((*l).clone()),
                _ => None,
            }
        }
        RangeOp::Exp(_) => {
            // <x|0> ** 0 = 1
            if matches!(r.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal)) {
                Some(Elem::from(Concrete::from(U256::from(1))))
            } else {
                None
            }
        }
        _ => None,
    }
}
