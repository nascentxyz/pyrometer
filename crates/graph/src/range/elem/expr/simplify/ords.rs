use crate::{
    nodes::Concrete,
    range::elem::{Elem, RangeElem},
};

use alloy_primitives::U256;
use shared::RangeArena;

pub struct Ords {
    pub x_ord_z: Option<std::cmp::Ordering>,
    pub y_ord_z: Option<std::cmp::Ordering>,
    pub y_ord_zero: Option<std::cmp::Ordering>,
    pub x_ord_zero: Option<std::cmp::Ordering>,
    pub z_ord_zero: Option<std::cmp::Ordering>,
    pub y_ord_one: Option<std::cmp::Ordering>,
    pub x_ord_one: Option<std::cmp::Ordering>,

    pub x_y_sign_match: Option<bool>,
    pub x_z_sign_match: Option<bool>,
    pub y_z_sign_match: Option<bool>,
}

#[allow(dead_code)]
impl Ords {
    pub fn new(
        x: &Elem<Concrete>,
        y: &Elem<Concrete>,
        z: &Elem<Concrete>,
        arena: &mut RangeArena<Elem<Concrete>>,
    ) -> Self {
        let zero = Elem::from(Concrete::from(U256::ZERO));
        let one = Elem::from(Concrete::from(U256::from(1)));
        let mut res = Self {
            x_ord_z: x.range_ord(z, arena),
            y_ord_z: y.range_ord(z, arena),
            y_ord_zero: y.range_ord(&zero, arena),
            x_ord_zero: x.range_ord(&zero, arena),
            z_ord_zero: z.range_ord(&zero, arena),
            y_ord_one: y.range_ord(&one, arena),
            x_ord_one: x.range_ord(&one, arena),
            x_y_sign_match: None,
            x_z_sign_match: None,
            y_z_sign_match: None,
        };
        if res.x_ord_zero.is_some() {
            res.x_y_sign_match = Some(res.x_ord_zero == res.y_ord_zero);
            res.x_z_sign_match = Some(res.x_ord_zero == res.z_ord_zero);
        }

        if res.y_ord_zero.is_some() {
            res.y_z_sign_match = Some(res.y_ord_zero == res.z_ord_zero);
        }
        res
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
