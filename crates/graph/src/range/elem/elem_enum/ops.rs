use crate::range::elem::{Elem, RangeExpr, RangeOp};

use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Rem, Shl, Shr, Sub};

impl<T: Ord> Add for Elem<T> {
    type Output = Self;

    fn add(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Sub for Elem<T> {
    type Output = Self;

    fn sub(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Mul for Elem<T> {
    type Output = Self;

    fn mul(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Div for Elem<T> {
    type Output = Self;

    fn div(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(false), other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Shl for Elem<T> {
    type Output = Self;

    fn shl(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shl, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Shr for Elem<T> {
    type Output = Self;

    fn shr(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shr, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> Rem for Elem<T> {
    type Output = Self;

    fn rem(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mod, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitAnd for Elem<T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitAnd, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitOr for Elem<T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitOr, other);
        Self::Expr(expr)
    }
}

impl<T: Ord> BitXor for Elem<T> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitXor, other);
        Self::Expr(expr)
    }
}
