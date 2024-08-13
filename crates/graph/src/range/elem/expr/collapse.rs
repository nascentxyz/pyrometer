use crate::elem::expr::simplify::*;

use crate::{
    nodes::Concrete,
    range::{
        elem::{Elem, RangeElem, RangeExpr, RangeOp},
        exec_traits::*,
    },
};

use ethers_core::types::U256;
use shared::RangeArena;

pub static ORD_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
    RangeOp::Min,
    RangeOp::Max,
];

pub static EQ_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
    RangeOp::And,
    RangeOp::Or,
];

pub static SINGLETON_EQ_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
];

pub static FLIP_INEQ_OPS: &[RangeOp] = &[RangeOp::Lt, RangeOp::Lte, RangeOp::Gt, RangeOp::Gte];

#[derive(Debug)]
pub enum MaybeCollapsed {
    Concretes(Elem<Concrete>, RangeOp, Elem<Concrete>),
    Collapsed(Elem<Concrete>),
    Not(Elem<Concrete>, RangeOp, Elem<Concrete>),
}

pub fn collapse(
    l: Elem<Concrete>,
    op: RangeOp,
    r: Elem<Concrete>,
    arena: &mut RangeArena<Elem<Concrete>>,
) -> MaybeCollapsed {
    tracing::trace!("collapsing: {l} {op} {r}");

    let l = if let Elem::Expr(e) = l {
        match collapse(*e.lhs, e.op, *e.rhs, arena) {
            MaybeCollapsed::Not(l, op, r) => Elem::Expr(RangeExpr::new(l, op, r)),
            MaybeCollapsed::Concretes(l, op, r) => Elem::Expr(RangeExpr::new(l, op, r)),
            MaybeCollapsed::Collapsed(e) => e,
        }
    } else {
        l
    };

    let r = if let Elem::Expr(e) = r {
        match collapse(*e.lhs, e.op, *e.rhs, arena) {
            MaybeCollapsed::Not(l, op, r) => Elem::Expr(RangeExpr::new(l, op, r)),
            MaybeCollapsed::Concretes(l, op, r) => Elem::Expr(RangeExpr::new(l, op, r)),
            MaybeCollapsed::Collapsed(e) => e,
        }
    } else {
        r
    };

    if let Some(e) = ident_rules(&l, op, &r, arena) {
        return MaybeCollapsed::Collapsed(e);
    }

    let res = match (l, r) {
        (l @ Elem::Arena(_), r) => {
            let t = l.dearenaize_clone(arena);
            match collapse(t, op, r, arena) {
                MaybeCollapsed::Not(l, op, r) => MaybeCollapsed::Not(l, op, r),
                MaybeCollapsed::Concretes(l, op, r) => MaybeCollapsed::Not(l, op, r),
                MaybeCollapsed::Collapsed(e) => MaybeCollapsed::Collapsed(e),
            }
        }
        (l, r @ Elem::Arena(_)) => {
            let t = r.dearenaize_clone(arena);
            match collapse(l, op, t, arena) {
                MaybeCollapsed::Not(l, op, r) => MaybeCollapsed::Not(l, op, r),
                MaybeCollapsed::Concretes(l, op, r) => MaybeCollapsed::Not(l, op, r),
                MaybeCollapsed::Collapsed(e) => MaybeCollapsed::Collapsed(e),
            }
        }
        (l @ Elem::Concrete(_), r @ Elem::Concrete(_)) => MaybeCollapsed::Concretes(l, op, r),
        (Elem::Expr(expr), d @ Elem::Reference(_)) => {
            // try to collapse the expression
            let x = &*expr.lhs;
            let y = &*expr.rhs;
            let z = d;

            let ords = Ords::new(x, y, &z, arena);

            match (expr.op, op) {
                (RangeOp::Sub(false), _) if ORD_OPS.contains(&op) => {
                    if let Some(res) = sub_ord_rules(x, y, op, &z, ords) {
                        MaybeCollapsed::Collapsed(res)
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Div(_), RangeOp::Eq) => {
                    if ords.x_eq_z() && !ords.y_eq_one() {
                        // (x -|/ y) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Add(_), RangeOp::Eq) => {
                    if (ords.x_eq_z() && !ords.y_eq_zero()) || (ords.y_eq_z() && !ords.x_eq_zero())
                    {
                        // (x +|* k) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Mul(_), RangeOp::Eq) => {
                    if (ords.x_eq_z() && !ords.y_eq_one()) || (ords.y_eq_z() && !ords.x_eq_one()) {
                        // (x +|* k) == x ==> false
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(false)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Max, RangeOp::Gte) => {
                    if ords.x_eq_z() || ords.y_eq_z() {
                        // max{ x, y } >= <x|y>
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(true)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Min, RangeOp::Lte) => {
                    if ords.x_eq_z() || ords.y_eq_z() {
                        // min{ x, y } <= <x|y>
                        MaybeCollapsed::Collapsed(Elem::from(Concrete::from(true)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                _ => MaybeCollapsed::Not(Elem::Expr(expr), op, z),
            }
        }
        // if we have an expression, it fundamentally must have a dynamic in it
        (Elem::Expr(expr), c @ Elem::Concrete(_)) => {
            // potentially collapsible
            let x = &*expr.lhs;
            let y = &*expr.rhs;
            let z = c;

            let ords = Ords::new(x, y, &z, arena);

            match (expr.op, op) {
                (RangeOp::Sub(false), _) if ORD_OPS.contains(&op) => {
                    if let Some(res) = sub_ord_rules(x, y, op, &z, ords) {
                        MaybeCollapsed::Collapsed(res)
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Add(false), _) if ORD_OPS.contains(&op) => {
                    if let Some(res) = add_ord_rules(x, y, op, &z, ords) {
                        MaybeCollapsed::Collapsed(res)
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Eq, RangeOp::Eq) => {
                    // ((x == y) == z)
                    // can skip if x and z eq
                    if (ords.x_eq_z() || ords.y_eq_z())
                        || z.range_eq(&Elem::from(Concrete::from(true)), arena)
                    {
                        MaybeCollapsed::Collapsed(Elem::Expr(expr))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Add(l_op), RangeOp::Add(r_op)) => {
                    // ((x + y) + z)
                    let op_fn = if l_op && r_op {
                        // unchecked
                        RangeAdd::range_wrapping_add
                    } else {
                        // checked
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                    };
                    if let Some(new) = op_fn(x, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(y.clone(), op, new)))
                    } else if let Some(new) = op_fn(y, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(x.clone(), op, new)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Add(l_op), RangeOp::Sub(r_op)) => {
                    // ((x + y) - z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(&z, arena) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && y >= z ==> x + (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(y, &z) {
                                    let new_expr =
                                        Elem::Expr(RangeExpr::new(x.clone(), expr.op, new));
                                    MaybeCollapsed::Collapsed(new_expr)
                                } else {
                                    MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                }
                            }
                            Some(std::cmp::Ordering::Less) => {
                                // y and z are concrete && y < z ==> x - (z - y)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(&z, y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        RangeOp::Sub(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                }
                            }
                            None => {
                                // x and z are concrete, if x >= z, just do (x - z) + y
                                // else do (y - (z - x))
                                match x.range_ord(&z, arena) {
                                    Some(std::cmp::Ordering::Equal)
                                    | Some(std::cmp::Ordering::Greater) => {
                                        let op_fn = if l_op {
                                            // unchecked
                                            RangeSub::range_wrapping_sub
                                        } else {
                                            // checked
                                            <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                        };
                                        if let Some(new) = op_fn(y, &z) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                x.clone(),
                                                expr.op,
                                                new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                        }
                                    }
                                    Some(std::cmp::Ordering::Less) => {
                                        // (y - (z - x)) because z > x, therefore its (-k + y) ==> (y - k) where k = (x - z)
                                        let op_fn = if l_op {
                                            // unchecked
                                            RangeSub::range_wrapping_sub
                                        } else {
                                            // checked
                                            <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                        };
                                        if let Some(new) = op_fn(&z, x) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                y.clone(),
                                                RangeOp::Sub(l_op),
                                                new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                        }
                                    }
                                    None => MaybeCollapsed::Not(Elem::Expr(expr), op, z),
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Sub(l_op), RangeOp::Add(r_op)) => {
                    // ((x - y) + z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(&z, arena) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && z <= y ==> x - (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(y, &z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        expr.op,
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                }
                            }
                            Some(std::cmp::Ordering::Less) => {
                                // y and z are concrete && y < z ==> x + (z - y)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(&z, y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        x.clone(),
                                        RangeOp::Add(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                }
                            }
                            None => {
                                // x and z are concrete, just add them ==> (x + z) - y
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeAdd::range_wrapping_add
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                                };
                                if let Some(new) = op_fn(x, &z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        new,
                                        expr.op,
                                        y.clone(),
                                    )))
                                } else {
                                    MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Mul(l_op), RangeOp::Mul(r_op)) => {
                    // ((x * y) * z)
                    if l_op == r_op {
                        let op_fn = if l_op {
                            // unchecked
                            RangeMul::range_wrapping_mul
                        } else {
                            // checked
                            <Elem<Concrete> as RangeMul<Concrete>>::range_mul
                        };
                        if let Some(new) = op_fn(x, &z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                y.clone(),
                                op,
                                new,
                            )))
                        } else if let Some(new) = op_fn(y, &z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                x.clone(),
                                op,
                                new,
                            )))
                        } else {
                            MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Add(wrapping), op) if EQ_OPS.contains(&op) => {
                    let const_op = if wrapping {
                        RangeSub::range_wrapping_sub
                    } else {
                        RangeSub::range_sub
                    };
                    // ((x + y) == z) => (x == (z - y)) || (y == (z - x))
                    // ..
                    // ((x + y) != z) => (x != (z - y)) || (y != (z - x))
                    if let Some(new) = const_op(&z, y) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(y.clone(), op, new)))
                    } else if let Some(new) = const_op(&z, x) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(x.clone(), op, new)))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Sub(wrapping), op) if EQ_OPS.contains(&op) => {
                    let op_y = if wrapping {
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_wrapping_add
                    } else {
                        <Elem<Concrete> as RangeAdd<Concrete>>::range_add
                    };
                    let op_x = if wrapping {
                        <Elem<Concrete> as RangeSub<Concrete>>::range_wrapping_sub
                    } else {
                        <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                    };
                    // ((x - y) == z) => (x == (z + y)) || (y == (x - z))
                    // ((x - y) != z) => (x != (z + y)) || (y != (x - z))
                    if let Some(new) = op_y(y, &z) {
                        let new_expr = RangeExpr::new(x.clone(), op, new);
                        MaybeCollapsed::Collapsed(Elem::Expr(new_expr))
                    } else if let Some(new) = op_x(x, &z) {
                        let new_expr = RangeExpr::new(y.clone(), op, new);
                        MaybeCollapsed::Collapsed(Elem::Expr(new_expr))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Mul(wrapping), op) if EQ_OPS.contains(&op) => {
                    let div_op = if wrapping {
                        RangeDiv::range_wrapping_div
                    } else {
                        RangeDiv::range_div
                    };
                    // ((x * y) == z) => (x == (z / y)) || (y == (z / x))
                    // ((x * y) != z) => (x != (z / y)) || (y != (z / x))
                    if let Some(new) = div_op(&z, x) {
                        let new_op = if ords.x_lt_zero() && FLIP_INEQ_OPS.contains(&op) {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            y.clone(),
                            new_op,
                            new,
                        )))
                    } else if let Some(new) = div_op(&z, y) {
                        let new_op = if ords.y_lt_zero() && FLIP_INEQ_OPS.contains(&op) {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            new_op,
                            new,
                        )))
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (RangeOp::Div(wrapping), op) if EQ_OPS.contains(&op) => {
                    let mul_op = if wrapping {
                        <Elem<Concrete> as RangeMul<Concrete>>::range_wrapping_mul
                    } else {
                        <Elem<Concrete> as RangeMul<Concrete>>::range_mul
                    };
                    let div_op = if wrapping {
                        <Elem<Concrete> as RangeDiv<Concrete>>::range_wrapping_div
                    } else {
                        <Elem<Concrete> as RangeDiv<Concrete>>::range_div
                    };

                    // ((x / y) == z) => (x == (z * y)) || (y == (x / z))
                    // ..
                    // ((x / y) != z) => (x != (z / y)) || (y != (x / z))
                    if let Some(new) = mul_op(&z, y) {
                        let new_op = if ords.y_lt_zero() && FLIP_INEQ_OPS.contains(&op) {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                            x.clone(),
                            new_op,
                            new,
                        )))
                    } else if !FLIP_INEQ_OPS.contains(&op) {
                        if let Some(new) = div_op(x, &z) {
                            // y is the dynamic element
                            // we cant do flip ops here because we do (x / y) * y >= z * y which is a flip potentially
                            // but we dont know if y was negative. so we limit to just eq & neq
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                y.clone(),
                                op,
                                new,
                            )))
                        } else {
                            MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (_, RangeOp::Eq) => {
                    // (x _ y) == z ==> (x _ y if z == true)
                    if z.range_eq(&Elem::from(Concrete::from(true)), arena) {
                        MaybeCollapsed::Collapsed(Elem::Expr(expr))
                    } else if z.range_eq(&Elem::from(Concrete::from(false)), arena) {
                        // (!x && !y)
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(Elem::Expr(expr), op, z),
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                (_, RangeOp::Neq) => {
                    // (x _ y) != z ==> (x _ y if z != false)
                    if z.range_eq(&Elem::from(Concrete::from(false)), arena) {
                        // != false is == true
                        MaybeCollapsed::Collapsed(Elem::Expr(expr))
                    } else if z.range_eq(&Elem::from(Concrete::from(true)), arena) {
                        // != true is == false, to make it == true, inverse everything
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(Elem::Expr(expr), op, z),
                        }
                    } else {
                        MaybeCollapsed::Not(Elem::Expr(expr), op, z)
                    }
                }
                _ => MaybeCollapsed::Not(Elem::Expr(expr), op, z),
            }
        }
        (l @ Elem::Concrete(_), r @ Elem::Expr(_)) => {
            if op.commutative() {
                match collapse(r, op, l, arena) {
                    MaybeCollapsed::Collapsed(inner) => MaybeCollapsed::Collapsed(inner.clone()),
                    MaybeCollapsed::Not(r, op, l) => MaybeCollapsed::Not(l, op, r),
                    MaybeCollapsed::Concretes(r, op, l) => MaybeCollapsed::Concretes(l, op, r),
                }
            } else if let Some(inv) = op.non_commutative_logical_inverse() {
                match collapse(r, inv, l, arena) {
                    MaybeCollapsed::Collapsed(inner) => MaybeCollapsed::Collapsed(inner.clone()),
                    MaybeCollapsed::Not(r, op, l) => MaybeCollapsed::Not(l, op, r),
                    MaybeCollapsed::Concretes(r, op, l) => MaybeCollapsed::Concretes(l, op, r),
                }
            } else {
                MaybeCollapsed::Not(l, op, r)
            }
        }
        (le @ Elem::Reference(_), c @ Elem::Concrete(_)) => {
            let zero = Elem::from(Concrete::from(U256::zero()));
            let one = Elem::from(Concrete::from(U256::one()));
            match op {
                RangeOp::Sub(_) | RangeOp::Add(_) => {
                    if matches!(c.range_ord(&zero, arena), Some(std::cmp::Ordering::Equal)) {
                        MaybeCollapsed::Collapsed(le.clone())
                    } else {
                        MaybeCollapsed::Not(le, op, c)
                    }
                }
                RangeOp::Mul(_) | RangeOp::Div(_) => {
                    if matches!(c.range_ord(&one, arena), Some(std::cmp::Ordering::Equal)) {
                        MaybeCollapsed::Collapsed(le.clone())
                    } else {
                        MaybeCollapsed::Not(le, op, c)
                    }
                }
                _ => MaybeCollapsed::Not(le, op, c),
            }
        }
        (Elem::Null, real) => match op {
            RangeOp::Max | RangeOp::Min => MaybeCollapsed::Collapsed(real.clone()),
            _ => MaybeCollapsed::Not(Elem::Null, op, real),
        },
        (real, Elem::Null) => match op {
            RangeOp::Max | RangeOp::Min => MaybeCollapsed::Collapsed(real.clone()),
            RangeOp::BitNot if matches!(real, Elem::Concrete(..)) => {
                MaybeCollapsed::Collapsed(real.range_bit_not().unwrap())
            }
            _ => MaybeCollapsed::Not(real, op, Elem::Null),
        },
        (l, r) => return MaybeCollapsed::Not(l, op, r),
    };

    match res {
        MaybeCollapsed::Not(ref l, op, ref r) => tracing::trace!("not result: {l} {op} {r}"),
        MaybeCollapsed::Concretes(ref l, op, ref r) => {
            tracing::trace!("concrete result: {l} {op} {r}")
        }
        MaybeCollapsed::Collapsed(ref l) => tracing::trace!("collapsed result: {l}"),
    }

    match res {
        MaybeCollapsed::Collapsed(Elem::Expr(e)) => collapse(*e.lhs, e.op, *e.rhs, arena),
        other => other,
    }
}
