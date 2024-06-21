use crate::elem::Elem;
use crate::exec_traits::RangeMemOps;
use crate::nodes::Concrete;

impl RangeMemOps<Concrete> for Elem<Concrete> {
    fn range_memcopy(&self) -> Option<Elem<Concrete>> {
        match self {
            Elem::Concrete(_a) => Some(self.clone()),
            Elem::ConcreteDyn(_a) => Some(self.clone()),
            _e => None,
        }
    }
}

pub fn exec_memcopy(
    lhs_min: &Elem<Concrete>,
    lhs_max: &Elem<Concrete>,
    maximize: bool,
) -> Option<Elem<Concrete>> {
    if maximize {
        Some(lhs_max.clone())
    } else {
        Some(lhs_min.clone())
    }
}
