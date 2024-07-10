use crate::{
    nodes::Concrete,
    range::{
        elem::expr::simplify::Ords,
        elem::{Elem, RangeConcrete, RangeExpr, RangeOp},
    },
};

pub fn sub_ord_rules(
    x: &Elem<Concrete>,
    y: &Elem<Concrete>,
    ord_op: RangeOp,
    z: &Elem<Concrete>,
    ords: Ords,
) -> Option<Elem<Concrete>> {
    match ord_op {
        RangeOp::Eq => {
            if !ords.x_eq_z() {
                return None;
            }
            // x - y == x
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
            // x - y != x
            //  ==> true iff y != 0, false otherwise
            let res = if ords.y_eq_zero() {
                Elem::from(false)
            } else {
                Elem::from(true)
            };
            Some(res)
        }
        RangeOp::Lt => {
            // x - y < z
            //  ==> true if:
            //       x <= z && y > 0
            //  ==> false if
            //      x == z && y < 0
            let x_lte_z = ords.x_eq_z() || ords.x_lt_z();
            if x_lte_z && ords.y_gt_zero() {
                Some(Elem::from(true))
            } else if ords.x_eq_z() && ords.y_lt_zero() {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Gt => {
            // x - y > z
            //  ==> true if:
            //       x > z && y <= 0 || x >= z && y < 0
            //  ==> false if
            //      x <= z && y > 0
            let true_lhs = ords.x_gt_z() && (ords.y_lt_zero() || ords.y_eq_zero());
            let true_rhs = (ords.x_gt_z() || ords.x_eq_z()) && ords.y_lt_zero();
            let x_lte_z = ords.x_eq_z() || ords.x_lt_z();

            if true_lhs || true_rhs {
                Some(Elem::from(true))
            } else if x_lte_z && ords.y_gt_zero() {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Lte => {
            // x - y <= z

            //  ==> true if:
            //       x <= z && y >= 0
            let x_lte_z = ords.x_eq_z() || ords.x_lt_z();
            let y_gte_zero = ords.y_gt_zero() || ords.y_eq_zero();

            //  ==> false if:
            //       x > z && y <= 0 || x >= z && y < 0
            let x_gt_z = ords.x_gt_z();
            let y_lte_zero = ords.y_lt_zero() || ords.y_eq_zero();
            let lhs = x_gt_z && y_lte_zero;

            let x_gte_z = ords.x_gt_z() || ords.x_eq_z();
            let y_lt_zero = ords.y_lt_zero();
            let rhs = x_gte_z && y_lt_zero;
            let false_cond = lhs || rhs;

            if x_lte_z && y_gte_zero {
                Some(Elem::from(true))
            } else if false_cond {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Gte => {
            // x - y >= z

            //  ==> true if:
            //       x >= z && y <= 0
            let x_gte_z = ords.x_eq_z() || ords.x_gt_z();
            let y_lte_zero = ords.y_lt_zero() || ords.y_eq_zero();

            //  ==> false if:
            //       x < z && y >= 0 || x <= z && y > 0
            let x_lt_z = ords.x_lt_z();
            let y_gte_zero = ords.y_gt_zero() || ords.y_eq_zero();
            let lhs = x_lt_z && y_gte_zero;

            let x_lte_z = ords.x_lt_z() || ords.x_eq_z();
            let y_gt_zero = ords.y_gt_zero();
            let rhs = x_lte_z && y_gt_zero;
            let false_cond = lhs || rhs;

            if x_gte_z && y_lte_zero {
                Some(Elem::from(true))
            } else if false_cond {
                Some(Elem::from(false))
            } else {
                None
            }
        }
        RangeOp::Max => {
            // max{x - y, z}
            // same as gt but return lhs or rhs instead
            match sub_ord_rules(x, y, RangeOp::Gt, z, ords) {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(b),
                    ..
                })) => {
                    if b {
                        Some(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            RangeOp::Sub(false),
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
            match sub_ord_rules(x, y, RangeOp::Lt, z, ords) {
                Some(Elem::Concrete(RangeConcrete {
                    val: Concrete::Bool(b),
                    ..
                })) => {
                    if b {
                        Some(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            RangeOp::Sub(false),
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
