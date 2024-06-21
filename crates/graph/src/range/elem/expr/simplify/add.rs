use crate::{
    nodes::Concrete,
    range::{
        elem::expr::simplify::Ords,
        elem::{Elem, RangeConcrete, RangeExpr, RangeOp},
    },
};

use shared::RangeArena;

pub fn add_ord_rules(
    x: &Elem<Concrete>,
    y: &Elem<Concrete>,
    ord_op: RangeOp,
    z: &Elem<Concrete>,
    ords: Ords,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> Option<Elem<Concrete>> {
    match ord_op {
        RangeOp::Eq => {
            if !ords.x_eq_z() {
                return None;
            }
            // x + y == x
            //  ==> true iff y == 0, false otherwise
            let res = if ords.y_eq_zero() {
                Elem::from(true)
            } else {
                Elem::from(false)
            };
            Some(res)
        }
        RangeOp::Neq => {
            if !ords.x_eq_z() {
                return None;
            }
            // x + y != x
            //  ==> true iff y != 0, false otherwise
            let res = if ords.y_eq_zero() {
                Elem::from(false)
            } else {
                Elem::from(true)
            };
            Some(res)
        }
        RangeOp::Lt => {
            // x + y < z
            //  ==> true if:
            //       x < z && y <= 0
            //  ==> false if
            //      x >= z && y > 0
            if ords.x_lt_z() && ords.y_lte_zero() {
                Some(Elem::from(true))
            } else if ords.x_gte_z() && ords.y_gt_zero() {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Gt => {
            // x + y > z
            //  ==> true if:
            //       x >= z && y > 0 || x > z && y >= 0
            let true_lhs = ords.x_gte_z() && ords.y_gt_zero();
            let true_rhs = ords.x_gt_z() && ords.y_gte_zero();
            //  ==> false if
            //      x <= z && y < 0
            let false_cond = ords.x_lte_z() && ords.y_lt_zero();

            if true_lhs || true_rhs {
                Some(Elem::from(true))
            } else if false_cond {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Lte => {
            // x + y <= z

            //  ==> true if:
            //       x <= z && y <= 0
            let true_cond = ords.x_lte_z() && ords.y_lte_zero();

            //  ==> false if:
            //       x > z && y >= 0 || x >= z && y > 0
            let false_lhs = ords.x_gt_z() && ords.y_gte_zero();
            let false_rhs = ords.x_gte_z() && ords.y_gt_zero();

            if true_cond {
                Some(Elem::from(true))
            } else if false_lhs || false_rhs {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Gte => {
            // x + y >= z

            //  ==> true if:
            //       x >= z && y >= 0
            let true_cond = ords.x_gte_z() && ords.y_gte_zero();

            //  ==> false if:
            //       x < z && y <= 0 || x <= z && y < 0
            let false_lhs = ords.x_lt_z() && ords.y_lte_zero();
            let false_rhs = ords.x_lte_z() && ords.y_lt_zero();

            if true_cond {
                Some(Elem::from(true))
            } else if false_lhs || false_rhs {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Max => {
            // max{x + y, z}
            // same as gt but return lhs or rhs instead
            match add_ord_rules(x, y, RangeOp::Gt, z, ords, arena) {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(b),
                    ..
                })) => {
                    if b {
                        Some(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            RangeOp::Add(false),
                            y.clone(),
                        )))
                    } else {
                        Some(z.clone())
                    }
                }
                _ => None,
            }
        }
        RangeOp::Min => {
            // min{x - y, z}
            // same as lt but return lhs or rhs instead
            match add_ord_rules(x, y, RangeOp::Lt, z, ords, arena) {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(b),
                    ..
                })) => {
                    if b {
                        Some(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            RangeOp::Add(false),
                            y.clone(),
                        )))
                    } else {
                        Some(z.clone())
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}
