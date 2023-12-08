use crate::{
    GraphBackend, GraphError, nodes::{Concrete, ContextVarNode},
    range::{elem::{RangeElem, RangeOp, Elem, MinMaxed}, exec_traits::*}
};

use shared::{NodeIdx};
use ethers_core::types::U256;

use std::collections::BTreeMap;


pub static SINGLETON_EQ_OPS: &[RangeOp] = &[
    RangeOp::Eq,
    RangeOp::Neq,
    RangeOp::Lt,
    RangeOp::Lte,
    RangeOp::Gt,
    RangeOp::Gte,
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

pub static FLIP_INEQ_OPS: &[RangeOp] = &[RangeOp::Lt, RangeOp::Lte, RangeOp::Gt, RangeOp::Gte];


/// A range expression composed of other range [`Elem`]
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeExpr<T> {
    pub maximized: Option<MinMaxed<T>>,
    pub minimized: Option<MinMaxed<T>>,
    pub lhs: Box<Elem<T>>,
    pub op: RangeOp,
    pub rhs: Box<Elem<T>>,
}

impl RangeExpr<Concrete> {
    pub fn inverse_if_boolean(&self) -> Option<Self> {
        if EQ_OPS.contains(&self.op) {
            if SINGLETON_EQ_OPS.contains(&self.op) {
                let mut new_self = self.clone();
                new_self.uncache();
                new_self.op = new_self.op.logical_inverse().unwrap();
                Some(new_self)
            } else {
                // non-singleton, i.e. AND or OR
                let mut new_self = self.clone();
                new_self.uncache();
                new_self.op = new_self.op.inverse().unwrap();
                if let Some(new_lhs) = new_self.inverse_if_boolean() {
                    *new_self.lhs = Elem::Expr(new_lhs);
                }
                if let Some(new_rhs) = new_self.inverse_if_boolean() {
                    *new_self.rhs = Elem::Expr(new_rhs);
                }
                Some(new_self)
            }
        } else {
            None
        }
    }
}

impl<T> RangeExpr<T> {
    /// Creates a new range expression given a left hand side range [`Elem`], a [`RangeOp`], and a a right hand side range [`Elem`].
    pub fn new(lhs: Elem<T>, op: RangeOp, rhs: Elem<T>) -> RangeExpr<T> {
        RangeExpr {
            maximized: None,
            minimized: None,
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        }
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.lhs.contains_node(node_idx) || self.rhs.contains_node(node_idx)
    }
}

impl RangeElem<Concrete> for RangeExpr<Concrete> {
    type GraphError = GraphError;
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn flatten(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Expr(RangeExpr::new(
            self.lhs.flatten(maximize, analyzer)?,
            self.op,
            self.rhs.flatten(maximize, analyzer)?,
        )))
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.dependent_on();
        deps.extend(self.rhs.dependent_on());
        deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        self.lhs.update_deps(mapping);
        self.rhs.update_deps(mapping);
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.lhs.filter_recursion(node_idx, new_idx);
        self.rhs.filter_recursion(node_idx, new_idx);
    }

    fn maximize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            Ok(*cached)
        } else {
            self.exec_op(true, analyzer)
        }
    }
    fn minimize(&self, analyzer: &impl GraphBackend) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            Ok(*cached)
        } else {
            self.exec_op(false, analyzer)
        }
    }

    fn simplify_maximize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        let l = self.lhs.simplify_maximize(exclude, analyzer)?;
        let r = self.rhs.simplify_maximize(exclude, analyzer)?;
        match collapse(l, self.op, r) {
            MaybeCollapsed::Collapsed(collapsed) => collapsed
                .expect_into_expr()
                .simplify_exec_op(true, exclude, analyzer),
            MaybeCollapsed::Not(l, r) => {
                RangeExpr::new(l, self.op, r).simplify_exec_op(true, exclude, analyzer)
            }
        }
    }
    fn simplify_minimize(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        let l = self.lhs.simplify_minimize(exclude, analyzer)?;
        let r = self.rhs.simplify_minimize(exclude, analyzer)?;
        match collapse(l, self.op, r) {
            MaybeCollapsed::Collapsed(collapsed) => Ok(collapsed),
            MaybeCollapsed::Not(l, r) => {
                RangeExpr::new(l, self.op, r).simplify_exec_op(false, exclude, analyzer)
            }
        }
    }

    fn cache_maximize(&mut self, g: &impl GraphBackend) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.cache_exec_op(true, g)?;
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphBackend) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.cache_exec_op(false, g)?;
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.uncache_exec();
    }

    fn contains_op_set(
        &self,
        max: bool,
        op_set: &[RangeOp],
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        if op_set.contains(&self.op) {
            Ok(true)
        } else {
            self.lhs.contains_op_set(max, op_set, analyzer)?;
            self.rhs.contains_op_set(max, op_set, analyzer)
        }
    }
}


enum MaybeCollapsed {
    Collapsed(Elem<Concrete>),
    Not(Elem<Concrete>, Elem<Concrete>),
}

fn collapse(l: Elem<Concrete>, op: RangeOp, r: Elem<Concrete>) -> MaybeCollapsed {
    let zero = Elem::from(Concrete::from(U256::zero()));
    match (l.clone(), r.clone()) {
        // if we have an expression, it fundamentally must have a dynamic in it
        (Elem::Expr(expr), c @ Elem::Concrete(_)) => {
            // potentially collapsible
            let x = expr.lhs;
            let y = expr.rhs;
            let z = c;
            match (expr.op, op) {
                (RangeOp::Eq, RangeOp::Eq) => {
                    // ((x == y) == z)
                    // can skip if x and z eq
                    if let Some(std::cmp::Ordering::Equal) = x.range_ord(&z) {
                        MaybeCollapsed::Collapsed(l)
                    } else if let Some(std::cmp::Ordering::Equal) = y.range_ord(&z) {
                        MaybeCollapsed::Collapsed(l)
                    } else if z.range_eq(&Elem::from(Concrete::from(true))) {
                        MaybeCollapsed::Collapsed(l)
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                    if let Some(new) = op_fn(&x, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, op, new)))
                    } else if let Some(new) = op_fn(&y, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Add(l_op), RangeOp::Sub(r_op)) => {
                    // ((x + y) - z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(&z) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && y >= z ==> x + (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(&y, &z) {
                                    let new_expr = Elem::Expr(RangeExpr::new(*x, expr.op, new));
                                    MaybeCollapsed::Collapsed(new_expr)
                                } else {
                                    MaybeCollapsed::Not(l, r)
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
                                if let Some(new) = op_fn(&z, &y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        *x,
                                        RangeOp::Sub(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                            None => {
                                // x and z are concrete, if x >= z, just do (x - z) + y
                                // else do (y - (z - x))
                                match x.range_ord(&z) {
                                    Some(std::cmp::Ordering::Equal)
                                    | Some(std::cmp::Ordering::Greater) => {
                                        let op_fn = if l_op {
                                            // unchecked
                                            RangeSub::range_wrapping_sub
                                        } else {
                                            // checked
                                            <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                        };
                                        if let Some(new) = op_fn(&y, &z) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                *x, expr.op, new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(l, r)
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
                                        if let Some(new) = op_fn(&z, &x) {
                                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                                *y,
                                                RangeOp::Sub(l_op),
                                                new,
                                            )))
                                        } else {
                                            MaybeCollapsed::Not(l, r)
                                        }
                                    }
                                    None => MaybeCollapsed::Not(l, r),
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (RangeOp::Sub(l_op), RangeOp::Add(r_op)) => {
                    // ((x - y) + z) => k - y || x + k
                    if l_op == r_op {
                        match y.range_ord(&z) {
                            Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) => {
                                // y and z are concrete && z <= y ==> x - (y - z)
                                let op_fn = if l_op {
                                    // unchecked
                                    RangeSub::range_wrapping_sub
                                } else {
                                    // checked
                                    <Elem<Concrete> as RangeSub<Concrete>>::range_sub
                                };
                                if let Some(new) = op_fn(&y, &z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        *x, expr.op, new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
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
                                if let Some(new) = op_fn(&z, &y) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        *x,
                                        RangeOp::Add(l_op),
                                        new,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
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
                                if let Some(new) = op_fn(&x, &z) {
                                    MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(
                                        new, expr.op, *y,
                                    )))
                                } else {
                                    MaybeCollapsed::Not(l, r)
                                }
                            }
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                        if let Some(new) = op_fn(&x, &z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, op, new)))
                        } else if let Some(new) = op_fn(&y, &z) {
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, op, new)))
                        } else {
                            MaybeCollapsed::Not(l, r)
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                    if let Some(new) = const_op(&z, &y) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, op, new)))
                    } else if let Some(new) = const_op(&z, &x) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                    if let Some(new) = op_x(&x, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, op, new)))
                    } else if let Some(new) = op_y(&y, &z) {
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                    if let Some(new) = div_op(&z, &x) {
                        let new_op = if matches!(x.range_ord(&zero), Some(std::cmp::Ordering::Less))
                            && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, new_op, new)))
                    } else if let Some(new) = div_op(&z, &y) {
                        let new_op = if matches!(y.range_ord(&zero), Some(std::cmp::Ordering::Less))
                            && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, new_op, new)))
                    } else {
                        MaybeCollapsed::Not(l, r)
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
                    if let Some(new) = mul_op(&z, &y) {
                        let new_op = if matches!(y.range_ord(&zero), Some(std::cmp::Ordering::Less))
                            && FLIP_INEQ_OPS.contains(&op)
                        {
                            op.inverse().unwrap()
                        } else {
                            op
                        };
                        MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*x, new_op, new)))
                    } else if !FLIP_INEQ_OPS.contains(&op) {
                        if let Some(new) = div_op(&x, &z) {
                            // y is the dynamic element
                            // we cant do flip ops here because we do (x / y) * y >= z * y which is a flip potentially
                            // but we dont know if y was negative. so we limit to just eq & neq
                            MaybeCollapsed::Collapsed(Elem::Expr(RangeExpr::new(*y, op, new)))
                        } else {
                            MaybeCollapsed::Not(l, r)
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (_, RangeOp::Eq) => {
                    // (x _ y) == z ==> (x _ y if z == true)
                    if z.range_eq(&Elem::from(Concrete::from(true))) {
                        MaybeCollapsed::Collapsed(l)
                    } else if z.range_eq(&Elem::from(Concrete::from(false))) {
                        // (!x && !y)
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(l, r),
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                (_, RangeOp::Neq) => {
                    // (x _ y) != z ==> (x _ y if z != false)
                    if z.range_eq(&Elem::from(Concrete::from(false))) {
                        // != false is == true
                        MaybeCollapsed::Collapsed(l)
                    } else if z.range_eq(&Elem::from(Concrete::from(true))) {
                        // != true is == false, to make it == true, inverse everything
                        match (
                            x.inverse_if_boolean(),
                            y.inverse_if_boolean(),
                            expr.op.logical_inverse(),
                        ) {
                            (Some(new_x), Some(new_y), Some(new_op)) => MaybeCollapsed::Collapsed(
                                Elem::Expr(RangeExpr::new(new_x, new_op, new_y)),
                            ),
                            _ => MaybeCollapsed::Not(l, r),
                        }
                    } else {
                        MaybeCollapsed::Not(l, r)
                    }
                }
                _ => MaybeCollapsed::Not(l, r),
            }
        }
        (Elem::Concrete(_c), Elem::Expr(_expr)) => match collapse(r.clone(), op, l.clone()) {
            collapsed @ MaybeCollapsed::Collapsed(_) => collapsed,
            MaybeCollapsed::Not(_, _) => MaybeCollapsed::Not(l, r),
        },
        _ => MaybeCollapsed::Not(l, r),
    }
}