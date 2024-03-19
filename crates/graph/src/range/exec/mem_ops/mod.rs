mod concat;
mod mem_set;

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
