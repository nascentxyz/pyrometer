mod impls;
mod ops;
mod range_elem;
mod traits;

use crate::range::elem::{RangeConcrete, RangeDyn, RangeExpr, Reference};

use shared::RangeArenaIdx;

/// A core range element.
#[derive(Default, Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Reference(Reference<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(RangeDyn<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    Concrete(RangeConcrete<T>),
    /// A range element that is an expression composed of other range elements
    Expr(RangeExpr<T>),
    /// A range element that is a pointer to another expression in an arena
    Arena(RangeArenaIdx),
    /// A null range element useful in range expressions that dont have a rhs
    #[default]
    Null,
}
