use crate::{
    nodes::{Concrete, ContextVarNode},
    range::elem::{Elem, RangeConcrete, RangeExpr, RangeOp, Reference},
};
use shared::NodeIdx;

use solang_parser::pt::Loc;

use std::{
    borrow::Cow,
    hash::{Hash, Hasher},
};

impl<T: Hash> Hash for Elem<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Elem::Reference(r) => r.hash(state),
            Elem::Concrete(c) => c.hash(state),
            Elem::Expr(expr) => expr.hash(state),
            Elem::ConcreteDyn(d) => d.hash(state),
            Elem::Null => (-1i32).hash(state),
            Elem::Arena(idx) => idx.hash(state),
        }
    }
}

impl<'a> Into<Cow<'a, Elem<Concrete>>> for &'a Elem<Concrete> {
    fn into(self) -> Cow<'a, Elem<Concrete>> {
        Cow::Borrowed(self)
    }
}

impl<'a> Into<Cow<'a, Elem<Concrete>>> for Elem<Concrete> {
    fn into(self) -> Cow<'a, Elem<Concrete>> {
        Cow::Owned(self)
    }
}

impl From<bool> for Elem<Concrete> {
    fn from(c: bool) -> Self {
        Elem::Concrete(RangeConcrete::new(Concrete::from(c), Loc::Implicit))
    }
}

impl<T> From<Reference<T>> for Elem<T> {
    fn from(dy: Reference<T>) -> Self {
        Elem::Reference(dy)
    }
}

impl<T> From<RangeConcrete<T>> for Elem<T> {
    fn from(c: RangeConcrete<T>) -> Self {
        Elem::Concrete(c)
    }
}

impl<T> From<NodeIdx> for Elem<T> {
    fn from(idx: NodeIdx) -> Self {
        Elem::Reference(Reference::new(idx))
    }
}

impl From<Concrete> for Elem<Concrete> {
    fn from(c: Concrete) -> Self {
        Elem::Concrete(RangeConcrete::new(c, Loc::Implicit))
    }
}

impl From<ContextVarNode> for Elem<Concrete> {
    fn from(c: ContextVarNode) -> Self {
        Elem::Reference(Reference::new(c.into()))
    }
}

impl std::fmt::Display for Elem<Concrete> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Elem::Reference(Reference { idx, .. }) => write!(f, "idx_{}", idx.index()),
            Elem::ConcreteDyn(d) => {
                write!(f, "{{len: {}, values: {{", d.len)?;
                d.val
                    .iter()
                    .try_for_each(|(key, (val, op))| write!(f, " {key}: ({val}, {op}),"))?;
                write!(f, "}}}}")
            }
            Elem::Concrete(RangeConcrete { val, .. }) => {
                write!(f, "{}", val.as_string())
            }
            Elem::Expr(RangeExpr { lhs, op, rhs, .. }) => match op {
                RangeOp::Min | RangeOp::Max => {
                    write!(f, "{}{{{}, {}}}", op.to_string(), lhs, rhs)
                }
                RangeOp::Cast => match &**rhs {
                    Elem::Concrete(RangeConcrete { val, .. }) => {
                        write!(
                            f,
                            "{}({}, {})",
                            op.to_string(),
                            lhs,
                            val.as_builtin().basic_as_string()
                        )
                    }
                    _ => write!(f, "{}({}, {})", op.to_string(), lhs, rhs),
                },
                RangeOp::BitNot => {
                    write!(f, "~{}", lhs)
                }
                _ => write!(f, "({} {} {})", lhs, op.to_string(), rhs),
            },
            Elem::Arena(idx) => write!(f, "arena_idx_{idx}"),
            Elem::Null => write!(f, "<null>"),
        }
    }
}
