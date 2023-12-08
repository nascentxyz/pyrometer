/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Reference(Reference<T>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(Box<RangeDyn<T>>),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    Concrete(RangeConcrete<T>),
    /// A range element that is an expression composed of other range elements
    Expr(RangeExpr<T>),
    /// A null range element useful in range expressions that dont have a rhs
    Null,
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

    pub fn expect_into_expr(self) -> RangeExpr<T> {
        match self {
            Self::Expr(expr) => expr,
            _ => panic!("Not expression"),
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

impl<T> Add for Elem<T> {
    type Output = Self;

    fn add(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Add(false), other);
        Self::Expr(expr)
    }
}

impl<T> Sub for Elem<T> {
    type Output = Self;

    fn sub(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Sub(false), other);
        Self::Expr(expr)
    }
}

impl<T> Mul for Elem<T> {
    type Output = Self;

    fn mul(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mul(false), other);
        Self::Expr(expr)
    }
}

impl<T> Div for Elem<T> {
    type Output = Self;

    fn div(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Div(false), other);
        Self::Expr(expr)
    }
}

impl<T> Shl for Elem<T> {
    type Output = Self;

    fn shl(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shl, other);
        Self::Expr(expr)
    }
}

impl<T> Shr for Elem<T> {
    type Output = Self;

    fn shr(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Shr, other);
        Self::Expr(expr)
    }
}

impl<T> Rem for Elem<T> {
    type Output = Self;

    fn rem(self, other: Elem<T>) -> Self {
        let expr = RangeExpr::new(self, RangeOp::Mod, other);
        Self::Expr(expr)
    }
}

impl<T> BitAnd for Elem<T> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitAnd, other);
        Self::Expr(expr)
    }
}

impl<T> BitOr for Elem<T> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitOr, other);
        Self::Expr(expr)
    }
}

impl<T> BitXor for Elem<T> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self::Output {
        let expr = RangeExpr::new(self, RangeOp::BitXor, other);
        Self::Expr(expr)
    }
}