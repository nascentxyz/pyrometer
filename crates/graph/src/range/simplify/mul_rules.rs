pub fn distribute(expr: Expression, distributed: Option<Elem<T>>) -> Elem<T> {
    match (
        expr.is_multiplication(),
        expr.lhs.is_const(),
        expr.rhs.is_const(),
    ) {
        (_, true, true) => expr.const_eval(),
        (false, _, _) => expr,
        (true, false, true) => {}
    }
}
