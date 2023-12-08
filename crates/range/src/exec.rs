/// For execution of operations to be performed on range expressions
pub trait ExecOp<T> {
    /// Attempts to execute ops by evaluating expressions and applying the op for the left-hand-side
    /// and right-hand-side
    fn exec_op(&self, maximize: bool, analyzer: &impl GraphLike) -> Result<Elem<T>, GraphError> {
        self.exec(self.spread(analyzer)?, maximize)
    }

    fn exec(
        &self,
        parts: (Elem<T>, Elem<T>, Elem<T>, Elem<T>),
        maximize: bool,
    ) -> Result<Elem<T>, GraphError>;
    /// Cache execution
    fn cache_exec_op(
        &mut self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<(), GraphError>;

    fn spread(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<(Elem<T>, Elem<T>, Elem<T>, Elem<T>), GraphError>;

    fn simplify_spread(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<((Elem<T>, Elem<T>, Elem<T>, Elem<T>), bool), GraphError>;

    fn uncache_exec(&mut self);

    fn simplify_exec_op(
        &self,
        maximize: bool,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<T>, GraphError>;

    /// Attempts to simplify an expression (i.e. just apply constant folding)
    fn simplify_exec(
        &self,
        parts: (Elem<T>, Elem<T>, Elem<T>, Elem<T>),
        maximize: bool,
    ) -> Result<Elem<T>, GraphError> {
        self.exec(parts, maximize)
    }
}

pub trait RangeAdd<T, Rhs = Self> {
    /// Perform addition between two range elements
    fn range_add(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_wrapping_add(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeSub<T, Rhs = Self> {
    /// Perform subtraction between two range elements
    fn range_sub(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_wrapping_sub(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeDiv<T, Rhs = Self> {
    /// Perform division between two range elements
    fn range_div(&self, other: &Rhs) -> Option<Elem<T>>;

    fn range_wrapping_div(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeExp<T, Rhs = Self> {
    /// Perform exponentiation between two range elements
    fn range_exp(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeMul<T, Rhs = Self> {
    /// Perform multiplication between two range elements
    fn range_mul(&self, other: &Rhs) -> Option<Elem<T>>;
    fn range_wrapping_mul(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeMod<T, Rhs = Self> {
    /// Perform modulo between two range elements
    fn range_mod(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeBitwise<T, Rhs = Self> {
    /// Perform a bitwise AND
    fn range_bit_and(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise OR
    fn range_bit_or(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise XOR
    fn range_bit_xor(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise NOT
    fn range_bit_not(&self) -> Option<Elem<T>>;
}

pub trait RangeShift<T, Rhs = Self> {
    /// Perform a bitwise shift left
    fn range_shl(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a bitwise shift right
    fn range_shr(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeCast<T, Rhs = Self> {
    /// Perform a cast on an element to the type of the right hand side
    fn range_cast(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeConcat<T, Rhs = Self> {
    /// Perform a cast on an element to the type of the right hand side
    fn range_concat(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeUnary<T, Rhs = Self> {
    /// Perform a logical NOT
    fn range_not(&self) -> Option<Elem<T>>;
    /// Perform a logical AND
    fn range_and(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical OR
    fn range_or(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeMax<T, Rhs = Self> {
    /// Take the maximum of two range elements
    fn range_max(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeMin<T, Rhs = Self> {
    /// Take the minimum of two range elements
    fn range_min(&self, other: &Rhs) -> Option<Elem<T>>;
}

pub trait RangeOrd<T, Rhs = Self> {
    /// Perform a logical equality test
    fn range_ord_eq(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical inequality test
    fn range_neq(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical greater than test
    fn range_gt(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical less than test
    fn range_lt(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical greater than or equal test
    fn range_gte(&self, other: &Rhs) -> Option<Elem<T>>;
    /// Perform a logical less than or equal test
    fn range_lte(&self, other: &Rhs) -> Option<Elem<T>>;
}
