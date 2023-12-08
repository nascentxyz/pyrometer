


impl ToRangeString for Elem<Concrete> {
    fn def_string(&self, analyzer: &impl GraphLike) -> RangeElemString {
        match self {
            Elem::Concrete(c) => RangeElemString::new(c.val.as_human_string(), c.loc),
            Elem::Reference(Reference { idx, .. }) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer)
                    .unwrap();
                RangeElemString::new(cvar.display_name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
            Elem::ConcreteDyn(rd) => rd.def_string(analyzer),
            Elem::Expr(expr) => expr.def_string(analyzer),
            Elem::Null => RangeElemString::new("null".to_string(), Loc::Implicit),
        }
    }

    fn to_range_string(&self, maximize: bool, analyzer: &impl GraphLike) -> RangeElemString {
        match self {
            Elem::Concrete(c) => RangeElemString::new(c.val.as_human_string(), c.loc),
            Elem::Reference(Reference { idx, .. }) => {
                let as_var = ContextVarNode::from(*idx);
                let name = as_var.display_name(analyzer).unwrap();
                RangeElemString::new(name, as_var.loc(analyzer).unwrap())
            }
            Elem::ConcreteDyn(rd) => rd.to_range_string(maximize, analyzer),
            Elem::Expr(expr) => expr.to_range_string(maximize, analyzer),
            Elem::Null => RangeElemString::new("null".to_string(), Loc::Implicit),
        }
    }
}

impl ToRangeString for RangeDyn<Concrete> {
    fn def_string(&self, analyzer: &impl GraphLike) -> RangeElemString {
        let displayed_vals = self
            .val
            .iter()
            .take(20)
            .map(|(key, val)| (key.minimize(analyzer).unwrap(), val))
            .collect::<BTreeMap<_, _>>();

        let val_str = displayed_vals
            .iter()
            .map(|(key, val)| {
                format!(
                    "{}: {}",
                    key.def_string(analyzer).s,
                    val.def_string(analyzer).s
                )
            })
            .collect::<Vec<_>>()
            .join(", ");

        RangeElemString::new(
            format!(
                "{{len: {}, indices: [{}]}}",
                self.len.to_range_string(false, analyzer).s,
                val_str
            ),
            self.loc,
        )
    }

    fn to_range_string(&self, maximize: bool, analyzer: &impl GraphLike) -> RangeElemString {
        let val_str = if self.val.len() > 10 {
            let displayed_vals = self
                .val
                .iter()
                .take(5)
                .map(|(key, val)| {
                    if maximize {
                        (key.maximize(analyzer).unwrap(), val)
                    } else {
                        (key.minimize(analyzer).unwrap(), val)
                    }
                })
                .collect::<BTreeMap<_, _>>();

            let val_str_head = displayed_vals
                .iter()
                .map(|(key, val)| {
                    format!(
                        "{}: {}",
                        key.def_string(analyzer).s,
                        val.def_string(analyzer).s
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");

            let displayed_vals_tail = self
                .val
                .iter()
                .rev()
                .take(5)
                .map(|(key, val)| {
                    if maximize {
                        (key.maximize(analyzer).unwrap(), val)
                    } else {
                        (key.minimize(analyzer).unwrap(), val)
                    }
                })
                .collect::<BTreeMap<_, _>>();

            let val_str_tail = displayed_vals_tail
                .iter()
                .map(|(key, val)| {
                    format!(
                        "{}: {}",
                        key.def_string(analyzer).s,
                        val.def_string(analyzer).s
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{val_str_head} ... {val_str_tail}")
        } else {
            let displayed_vals = self
                .val
                .iter()
                .take(10)
                .map(|(key, val)| {
                    if maximize {
                        (key.maximize(analyzer).unwrap(), val)
                    } else {
                        (key.minimize(analyzer).unwrap(), val)
                    }
                })
                .collect::<BTreeMap<_, _>>();

            displayed_vals
                .iter()
                .map(|(key, val)| {
                    format!(
                        "{}: {}",
                        key.def_string(analyzer).s,
                        val.def_string(analyzer).s
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        };

        RangeElemString::new(
            format!(
                "{{len: {}, indices: {{{}}}}}",
                self.len.to_range_string(maximize, analyzer).s,
                val_str
            ),
            self.loc,
        )
    }
}

impl ToRangeString for RangeExpr<Concrete> {
    fn def_string(&self, analyzer: &impl GraphLike) -> RangeElemString {
        self.lhs.def_string(analyzer)
    }

    fn to_range_string(&self, maximize: bool, analyzer: &impl GraphLike) -> RangeElemString {
        let lhs_r_str = self.lhs.to_range_string(maximize, analyzer);
        let lhs_str = match *self.lhs {
            Elem::Expr(_) => {
                let new_str = format!("({})", lhs_r_str.s);
                RangeElemString::new(new_str, lhs_r_str.loc)
            }
            _ => lhs_r_str,
        };

        let rhs_r_str = self.rhs.to_range_string(maximize, analyzer);

        let rhs_str = match *self.rhs {
            Elem::Expr(_) => {
                let new_str = format!("({})", rhs_r_str.s);
                RangeElemString::new(new_str, rhs_r_str.loc)
            }
            _ => rhs_r_str,
        };

        if matches!(self.op, RangeOp::Min | RangeOp::Max) {
            RangeElemString::new(
                format!("{}{{{}, {}}}", self.op.to_string(), lhs_str.s, rhs_str.s),
                lhs_str.loc,
            )
        } else if matches!(self.op, RangeOp::Cast | RangeOp::Concat) {
            let rhs = if maximize {
                self.rhs.maximize(analyzer).unwrap()
            } else {
                self.rhs.minimize(analyzer).unwrap()
            };

            match rhs {
                Elem::Concrete(c) => RangeElemString::new(
                    format!(
                        "{}({})",
                        c.val.as_builtin().as_string(analyzer).unwrap(),
                        lhs_str.s
                    ),
                    lhs_str.loc,
                ),
                _ => RangeElemString::new(
                    format!("{}({}, {})", self.op.to_string(), lhs_str.s, rhs_str.s),
                    lhs_str.loc,
                ),
            }
        } else if matches!(self.op, RangeOp::BitNot) {
            let lhs = if maximize {
                self.lhs.maximize(analyzer).unwrap()
            } else {
                self.lhs.minimize(analyzer).unwrap()
            };

            match lhs {
                Elem::Concrete(_c) => RangeElemString::new(format!("~{}", lhs_str.s), lhs_str.loc),
                _ => RangeElemString::new(format!("~{}", lhs_str.s), lhs_str.loc),
            }
        } else {
            RangeElemString::new(
                format!("{} {} {}", lhs_str.s, self.op.to_string(), rhs_str.s),
                lhs_str.loc,
            )
        }
    }
}
