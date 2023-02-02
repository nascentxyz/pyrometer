use crate::range::elem::RangeElem;
use crate::range::elem_ty::Dynamic;
use crate::range::elem_ty::RangeExpr;
use crate::range::elem::RangeOp;
use crate::context::ContextVarNode;
use crate::Concrete;
use crate::range::Elem;
use crate::analyzer::AnalyzerLike;
use solang_parser::pt::Loc;

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeElemString {
    pub s: String,
    pub loc: Loc,
}

impl RangeElemString {
    pub fn new(s: String, loc: Loc) -> Self {
        Self { s, loc }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RangeString {
    pub min: RangeElemString,
    pub max: RangeElemString,
}

impl RangeString {
    pub fn new(min: RangeElemString, max: RangeElemString) -> Self {
        Self { min, max }
    }
}

pub trait ToRangeString {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString;
    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString;
}


impl ToRangeString for Elem<Concrete> {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
        	Elem::Concrete(c) => RangeElemString::new(c.val.as_human_string(), c.loc),
            Elem::Dynamic(Dynamic{ idx, .. }) => {
                let cvar = ContextVarNode::from(*idx)
                    .first_version(analyzer)
                    .underlying(analyzer);
                RangeElemString::new(cvar.display_name.clone(), cvar.loc.unwrap_or(Loc::Implicit))
            }
            Elem::Expr(expr) => expr.def_string(analyzer),
            Elem::Null => RangeElemString::new("".to_string(), Loc::Implicit)
        }
    }

    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        match self {
            Elem::Concrete(c) => RangeElemString::new(c.val.as_human_string(), c.loc),
            Elem::Dynamic(Dynamic { idx, side: _, loc }) => {
                let as_var = ContextVarNode::from(*idx);
                let name = format!(
                    "{}",
                    as_var.display_name(analyzer),
                );
                RangeElemString::new(name, *loc)
            }
            Elem::Expr(expr) => expr.to_range_string(analyzer),
            Elem::Null => RangeElemString::new("".to_string(), Loc::Implicit)
        }
    }
}

impl ToRangeString for RangeExpr<Concrete> {
    fn def_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
    	self.lhs.def_string(analyzer)
    }

    fn to_range_string(&self, analyzer: &impl AnalyzerLike) -> RangeElemString {
        let lhs_r_str = self.lhs.to_range_string(analyzer);
        let lhs_str = match *self.lhs {
            Elem::Expr(_) => {
                let new_str = format!("({})", lhs_r_str.s);
                RangeElemString::new(new_str, lhs_r_str.loc)
            }
            _ => lhs_r_str,
        };

        let rhs_r_str = self.rhs.to_range_string(analyzer);

        let rhs_str = match *self.rhs {
            Elem::Expr(_) => {
                let new_str = format!("({})", rhs_r_str.s);
                RangeElemString::new(new_str, rhs_r_str.loc)
            }
            _ => rhs_r_str,
        };

        if matches!(self.op, RangeOp::Min | RangeOp::Max) {
            RangeElemString::new(
                format!("{}({}, {})", self.op.to_string(), lhs_str.s, rhs_str.s),
                lhs_str.loc,
            )
        } else if matches!(self.op, RangeOp::Cast) {
            match self.rhs.eval(analyzer) {
                Elem::Concrete(c) => {
                    RangeElemString::new(
                        format!("{}({})", c.val.as_builtin().as_string(), lhs_str.s),
                        lhs_str.loc,
                    )
                }
                _ => {
                    RangeElemString::new(
                        format!("{}({}, {})", self.op.to_string(), lhs_str.s, rhs_str.s),
                        lhs_str.loc,
                    )
                }
            }
        } else {
            RangeElemString::new(
                format!("{} {} {}", lhs_str.s, self.op.to_string(), rhs_str.s),
                lhs_str.loc,
            )
        }
    }
}