use crate::{
    nodes::Concrete,
    range::{
        elem::{Elem, RangeConcrete, RangeElem, RangeExpr, RangeOp},
        exec_traits::*,
    },
    GraphBackend,
};

use ethers_core::types::U256;
use shared::RangeArena;

use std::borrow::Cow;

pub struct Ords {
    pub x_ord_z: Option<std::cmp::Ordering>,
    pub y_ord_z: Option<std::cmp::Ordering>,
    pub y_ord_zero: Option<std::cmp::Ordering>,
    pub x_ord_zero: Option<std::cmp::Ordering>,
    pub y_ord_one: Option<std::cmp::Ordering>,
    pub x_ord_one: Option<std::cmp::Ordering>,
}

impl Ords {
    pub fn new(
        x: &Elem<Concrete>,
        y: &Elem<Concrete>,
        z: &Elem<Concrete>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Self {
        let zero = Elem::from(Concrete::from(U256::zero()));
        let one = Elem::from(Concrete::from(U256::one()));
        Self {
            x_ord_z: x.range_ord(z, arena),
            y_ord_z: y.range_ord(z, arena),
            y_ord_zero: y.range_ord(&zero, arena),
            x_ord_zero: x.range_ord(&zero, arena),
            y_ord_one: y.range_ord(&one, arena),
            x_ord_one: x.range_ord(&one, arena),
        }
    }

    pub fn x_gte_z(&self) -> bool {
        self.x_gt_z() || self.x_eq_z()
    }
    pub fn y_gte_z(&self) -> bool {
        self.y_gt_z() || self.y_eq_z()
    }

    pub fn x_lte_z(&self) -> bool {
        self.x_lt_z() || self.x_eq_z()
    }
    pub fn y_lte_z(&self) -> bool {
        self.y_lt_z() || self.y_eq_z()
    }

    pub fn x_gt_z(&self) -> bool {
        matches!(self.x_ord_z, Some(std::cmp::Ordering::Greater))
    }

    pub fn y_gt_z(&self) -> bool {
        matches!(self.x_ord_z, Some(std::cmp::Ordering::Greater))
    }

    pub fn x_lt_z(&self) -> bool {
        matches!(self.x_ord_z, Some(std::cmp::Ordering::Less))
    }

    pub fn y_lt_z(&self) -> bool {
        matches!(self.x_ord_z, Some(std::cmp::Ordering::Less))
    }

    pub fn x_eq_z(&self) -> bool {
        matches!(self.x_ord_z, Some(std::cmp::Ordering::Equal))
    }

    pub fn y_eq_z(&self) -> bool {
        matches!(self.y_ord_z, Some(std::cmp::Ordering::Equal))
    }

    pub fn x_lt_zero(&self) -> bool {
        matches!(self.x_ord_zero, Some(std::cmp::Ordering::Less))
    }

    pub fn y_lt_zero(&self) -> bool {
        matches!(self.y_ord_zero, Some(std::cmp::Ordering::Less))
    }

    pub fn x_eq_zero(&self) -> bool {
        matches!(self.x_ord_zero, Some(std::cmp::Ordering::Equal))
    }

    pub fn x_gt_zero(&self) -> bool {
        matches!(self.x_ord_zero, Some(std::cmp::Ordering::Greater))
    }

    pub fn y_gt_zero(&self) -> bool {
        matches!(self.y_ord_zero, Some(std::cmp::Ordering::Greater))
    }

    pub fn y_eq_zero(&self) -> bool {
        matches!(self.y_ord_zero, Some(std::cmp::Ordering::Equal))
    }

    pub fn x_gte_zero(&self) -> bool {
        self.x_gt_zero() || self.x_eq_zero()
    }

    pub fn y_gte_zero(&self) -> bool {
        self.y_gt_zero() || self.y_eq_zero()
    }

    pub fn x_lte_zero(&self) -> bool {
        self.x_lt_zero() || self.x_eq_zero()
    }

    pub fn y_lte_zero(&self) -> bool {
        self.y_lt_zero() || self.y_eq_zero()
    }

    pub fn x_eq_one(&self) -> bool {
        matches!(self.x_ord_one, Some(std::cmp::Ordering::Equal))
    }

    pub fn y_eq_one(&self) -> bool {
        matches!(self.y_ord_one, Some(std::cmp::Ordering::Equal))
    }
}
