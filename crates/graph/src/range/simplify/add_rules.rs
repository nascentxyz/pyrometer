pub fn add_zero(expr: Expression) -> Elem<T> {
    match (expr.is_addition(), expr.lhs.is_zero(), expr.rhs.is_zero()) {
        (false, _, _) => expr,
        (true, true, true) => Elem::zero(),
        (true, true, _) => expr.rhs,
        (true, _, true) => expr.lhs,
    }
}
