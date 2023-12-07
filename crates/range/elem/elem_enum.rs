
/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Reference(Reference),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(Box<RangeDyn<T>>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    Concrete(RangeConcrete<T>),
    /// A range element that is an expression composed of other range elements
    Expr(RangeExpr<T>),
    /// A null range element useful in range expressions that dont have a rhs
    Null,
}

impl std::fmt::Display for Elem<Concrete> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Elem::Reference(Reference { idx, .. }) => write!(f, "idx_{}", idx.index()),
            Elem::ConcreteDyn(..) => write!(f, "range_elem"),
            Elem::Concrete(RangeConcrete { val, .. }) => {
                write!(f, "{}", val.as_string())
            }
            Elem::Expr(RangeExpr { lhs, op, rhs, .. }) => {
                write!(f, "({} {} {})", op.to_string(), lhs, rhs)
            }
            _ => write!(f, ""),
        }
    }
}

impl From<Concrete> for Elem<Concrete> {
    fn from(c: Concrete) -> Self {
        Elem::Concrete(RangeConcrete {
            val: c,
            loc: Loc::Implicit,
        })
    }
}

impl From<ContextVarNode> for Elem<Concrete> {
    fn from(c: ContextVarNode) -> Self {
        Elem::Reference(Reference::new(c.into()))
    }
}

impl From<NodeIdx> for Elem<Concrete> {
    fn from(idx: NodeIdx) -> Self {
        Elem::Reference(Reference::new(idx))
    }
}

impl<T> Elem<T> {
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        match self {
            Self::Reference(d) => d.idx == node_idx,
            Self::Concrete(_) => false,
            Self::Expr(expr) => expr.contains_node(node_idx),
            Self::ConcreteDyn(d) => d.contains_node(node_idx),
            Self::Null => false,
        }
    }

    pub fn dyn_map(&self) -> Option<&BTreeMap<Self, Self>> {
        match self {
            Self::ConcreteDyn(dyn_range) => Some(&dyn_range.val),
            _ => None,
        }
    }

    pub fn dyn_map_mut(&mut self) -> Option<&mut BTreeMap<Self, Self>> {
        match self {
            Self::ConcreteDyn(ref mut dyn_range) => Some(&mut dyn_range.val),
            _ => None,
        }
    }

    /// Creates a new range element that is a cast from one type to another
    pub fn cast(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Cast, other);
        Elem::Expr(expr)
    }

    pub fn concat(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Concat, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the minimum of two range elements
    pub fn min(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Min, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the maximum of two range elements
    pub fn max(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Max, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of equality of two range elements
    pub fn eq(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Eq, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of inequality of two range elements
    pub fn neq(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Neq, other);
        Elem::Expr(expr)
    }

    /// Creates a new range element that is one range element to the power of another
    pub fn pow(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Exp, other);
        Elem::Expr(expr)
    }
}

impl<T> From<Reference> for Elem<T> {
    fn from(dy: Reference) -> Self {
        Elem::Reference(dy)
    }
}

impl<T> From<RangeConcrete<T>> for Elem<T> {
    fn from(c: RangeConcrete<T>) -> Self {
        Elem::Concrete(c)
    }
}

impl Elem<Concrete> {
    pub fn node_idx(&self) -> Option<NodeIdx> {
        match self {
            Self::Reference(Reference { idx, .. }) => Some(*idx),
            _ => None,
        }
    }

    pub fn concrete(&self) -> Option<Concrete> {
        match self {
            Self::Concrete(RangeConcrete { val: c, .. }) => Some(c.clone()),
            _ => None,
        }
    }

    pub fn is_negative(
        &self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        let res = match self {
            Elem::Concrete(RangeConcrete {
                val: Concrete::Int(_, val),
                ..
            }) if val < &I256::zero() => true,
            Elem::Reference(dy) => {
                if maximize {
                    dy.maximize(analyzer)?.is_negative(maximize, analyzer)?
                } else {
                    dy.minimize(analyzer)?.is_negative(maximize, analyzer)?
                }
            }
            Elem::Expr(expr) => {
                if maximize {
                    expr.maximize(analyzer)?.is_negative(maximize, analyzer)?
                } else {
                    expr.minimize(analyzer)?.is_negative(maximize, analyzer)?
                }
            }
            _ => false,
        };
        Ok(res)
    }

    pub fn pre_evaled_is_negative(&self) -> bool {
        matches!(self, Elem::Concrete(RangeConcrete { val: Concrete::Int(_, val), ..}) if val < &I256::zero())
    }

    pub fn maybe_concrete(&self) -> Option<RangeConcrete<Concrete>> {
        match self {
            Elem::Concrete(a) => Some(a.clone()),
            _ => None,
        }
    }

    pub fn maybe_range_dyn(&self) -> Option<RangeDyn<Concrete>> {
        match self {
            Elem::ConcreteDyn(a) => Some(*a.clone()),
            _ => None,
        }
    }
}

impl RangeElem<Concrete> for Elem<Concrete> {
    fn range_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Concrete(a), Self::Concrete(b)) => a.range_eq(b),
            _ => false,
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Concrete(a), Self::Concrete(b)) => {
                let ord = a.range_ord(b);
                if ord.is_none() {
                    println!("couldnt compare: {a:?} {b:?}");
                }

                ord
            }
            _ => None,
        }
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        match self {
            Self::Reference(d) => d.dependent_on(),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(),
            Self::ConcreteDyn(d) => d.dependent_on(),
            Self::Null => vec![],
        }
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        match self {
            Self::Reference(d) => d.update_deps(mapping),
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.update_deps(mapping),
            Self::ConcreteDyn(d) => d.update_deps(mapping),
            Self::Null => {}
        }
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        match self {
            Self::Reference(ref mut d) => {
                if d.idx == node_idx {
                    d.idx = new_idx
                }
            }
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.filter_recursion(node_idx, new_idx),
            Self::ConcreteDyn(d) => d.filter_recursion(node_idx, new_idx),
            Self::Null => {}
        }
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.maximize(analyzer)?,
            Concrete(inner) => inner.maximize(analyzer)?,
            ConcreteDyn(inner) => inner.maximize(analyzer)?,
            Expr(expr) => expr.maximize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.minimize(analyzer)?,
            Concrete(inner) => inner.minimize(analyzer)?,
            ConcreteDyn(inner) => inner.minimize(analyzer)?,
            Expr(expr) => expr.minimize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.simplify_maximize(analyzer)?,
            Concrete(inner) => inner.simplify_maximize(analyzer)?,
            ConcreteDyn(inner) => inner.simplify_maximize(analyzer)?,
            Expr(expr) => expr.simplify_maximize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Reference(dy) => dy.simplify_minimize(analyzer)?,
            Concrete(inner) => inner.simplify_minimize(analyzer)?,
            ConcreteDyn(inner) => inner.simplify_minimize(analyzer)?,
            Expr(expr) => expr.simplify_minimize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn cache_maximize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_maximize(analyzer),
            Concrete(inner) => inner.cache_maximize(analyzer),
            ConcreteDyn(inner) => inner.cache_maximize(analyzer),
            Expr(expr) => expr.cache_maximize(analyzer),
            Null => Ok(()),
        }
    }

    fn cache_minimize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Reference(dy) => dy.cache_minimize(analyzer),
            Concrete(inner) => inner.cache_minimize(analyzer),
            ConcreteDyn(inner) => inner.cache_minimize(analyzer),
            Expr(expr) => expr.cache_minimize(analyzer),
            Null => Ok(()),
        }
    }
    fn uncache(&mut self) {
        use Elem::*;
        match self {
            Reference(dy) => dy.uncache(),
            Concrete(inner) => inner.uncache(),
            ConcreteDyn(inner) => inner.uncache(),
            Expr(expr) => expr.uncache(),
            Null => {}
        }
    }
}

impl Add for Elem<Concrete> {
    type Output = Self;

    fn add(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(false), other);
        Self::Expr(expr)
    }
}

impl Sub for Elem<Concrete> {
    type Output = Self;

    fn sub(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(false), other);
        Self::Expr(expr)
    }
}

impl Mul for Elem<Concrete> {
    type Output = Self;

    fn mul(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(false), other);
        Self::Expr(expr)
    }
}

impl Div for Elem<Concrete> {
    type Output = Self;

    fn div(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(false), other);
        Self::Expr(expr)
    }
}

impl Shl for Elem<Concrete> {
    type Output = Self;

    fn shl(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shl, other);
        Self::Expr(expr)
    }
}

impl Shr for Elem<Concrete> {
    type Output = Self;

    fn shr(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shr, other);
        Self::Expr(expr)
    }
}

impl Rem for Elem<Concrete> {
    type Output = Self;

    fn rem(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mod, other);
        Self::Expr(expr)
    }
}

impl BitAnd for Elem<Concrete> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitAnd, other);
        Self::Expr(expr)
    }
}

impl BitOr for Elem<Concrete> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitOr, other);
        Self::Expr(expr)
    }
}

impl BitXor for Elem<Concrete> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitXor, other);
        Self::Expr(expr)
    }
}

impl Elem<Concrete> {
    pub fn wrapping_add(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_sub(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_mul(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(true), other);
        Self::Expr(expr)
    }
    pub fn wrapping_div(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(true), other);
        Self::Expr(expr)
    }

    /// Creates a logical AND of two range elements
    pub fn and(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::And, other);
        Self::Expr(expr)
    }

    /// Creates a logical OR of two range elements
    pub fn or(self, other: Self) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Or, other);
        Self::Expr(expr)
    }

    pub fn maybe_elem_min(&self) -> Option<Self> {
        match self {
            Elem::Concrete(RangeConcrete { val, .. }) => Some(Elem::from(Concrete::min(val)?)),
            _ => None,
        }
    }

    pub fn maybe_elem_max(&self) -> Option<Self> {
        match self {
            Elem::Concrete(RangeConcrete { val, .. }) => Some(Elem::from(Concrete::max(val)?)),
            _ => None,
        }
    }
}