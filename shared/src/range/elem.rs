use crate::NodeIdx;
use crate::GraphLike;
use std::collections::BTreeMap;
use crate::context::ContextVarNode;
use crate::range::elem_ty::RangeExpr;
use crate::range::elem_ty::Elem;
use crate::analyzer::AnalyzerLike;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RangeOp {
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    Min,
    Max,
    Lt,
    Lte,
    Gt,
    Gte,
    Eq,
    Neq,
    Not,
    Shl,
    Shr,
    And,
    Where,
    Cast,
    BitAnd,
    Exp,
}


impl RangeOp {
    pub fn inverse(self) -> Option<Self> {
        use RangeOp::*;
        match self {
            Add => Some(Sub),
            Mul => Some(Div),
            Sub => Some(Add),
            Div => Some(Mul),
            Shl => Some(Shr),
            Shr => Some(Shl),
            Eq => Some(Neq),
            Neq => Some(Eq),
            _ => None
            // e => panic!("tried to inverse unreversable op: {:?}", e),
        }
    }
}

impl ToString for RangeOp {
    fn to_string(&self) -> String {
        use RangeOp::*;
        match self {
            Add => "+".to_string(),
            Mul => "*".to_string(),
            Sub => "-".to_string(),
            Div => "/".to_string(),
            Shl => "<<".to_string(),
            Shr => ">>".to_string(),
            Mod => "%".to_string(),
            Exp => "**".to_string(),
            Min => "min".to_string(),
            Max => "max".to_string(),
            Lt => "<".to_string(),
            Gt => ">".to_string(),
            Lte => "<=".to_string(),
            Gte => ">=".to_string(),
            Eq => "==".to_string(),
            Neq => "!=".to_string(),
            Not => "!".to_string(),
            And => "&".to_string(),
            Where => "where".to_string(),
            Cast => "cast".to_string(),
            BitAnd => "&".to_string(),
        }
    }
}


pub trait RangeElem<T> {
	fn eval(&self, analyzer: &impl GraphLike) -> Elem<T>;
    fn simplify(&self, analyzer: &impl GraphLike) -> Elem<T>;
    fn range_eq(&self, other: &Self, analyzer: &impl GraphLike) -> bool;
    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering>;
    fn range_op(lhs: Elem<T>, rhs: Elem<T>, op: RangeOp) -> Elem<T> where Self: Sized {
        Elem::Expr(RangeExpr::new(lhs, op, rhs))
    }
    fn dependent_on(&self) -> Vec<ContextVarNode>;
    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>);
    fn filter_recursion(&mut self, node_idx: NodeIdx, old: Elem<T>);
}


