use crate::analyzer::GraphError;
use crate::context::ContextVarNode;
use crate::nodes::{TypeNode, VarType};
use crate::range::range_ops::*;
use crate::range::Range;
use crate::range::{elem::RangeOp, *};
use crate::{Concrete, NodeIdx};
use solang_parser::pt::Loc;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::*;
use std::rc::Rc;

/// A dynamic range element value
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct Dynamic {
    /// Index of the node that is referenced
    pub idx: NodeIdx,
    pub minimized: Option<MinMaxed<Concrete>>,
    pub maximized: Option<MinMaxed<Concrete>>,
}

impl Dynamic {
    pub fn new(idx: NodeIdx) -> Self {
        Self {
            idx,
            minimized: None,
            maximized: None,
        }
    }
}

impl RangeElem<Concrete> for Dynamic {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        vec![ContextVarNode::from(self.idx)]
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        if let Some(new) = mapping.get(&ContextVarNode::from(self.idx)) {
            self.idx = NodeIdx::from(new.0);
        }
    }

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx) {}

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok((*cached).clone());
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_max(analyzer)
                } else {
                    Ok(Elem::Dynamic(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Dynamic(self.clone())),
        }
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok((*cached).clone());
        }

        let cvar = ContextVarNode::from(self.idx).underlying(analyzer)?;
        match &cvar.ty {
            VarType::User(TypeNode::Contract(_), maybe_range)
            | VarType::User(TypeNode::Enum(_), maybe_range)
            | VarType::User(TypeNode::Ty(_), maybe_range)
            | VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_min(analyzer)
                } else {
                    Ok(Elem::Dynamic(self.clone()))
                }
            }
            VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
                val: concrete_node.underlying(analyzer)?.clone(),
                loc: cvar.loc.unwrap_or(Loc::Implicit),
            })),
            _e => Ok(Elem::Dynamic(self.clone())),
        }
    }

    fn simplify_maximize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        // let cvar = ContextVarNode::from(self.idx);
        // if cvar.is_symbolic(analyzer)? {
        Ok(Elem::Dynamic(self.clone()))
        // }
        // if !cvar.is_tmp(analyzer)? {
        //     return Ok(Elem::Dynamic(self.clone()))
        // }
        // let cvar = cvar.underlying(analyzer)?;
        // match &cvar.ty {
        //     VarType::User(TypeNode::Contract(_), maybe_range)
        //     | VarType::User(TypeNode::Enum(_), maybe_range)
        //     | VarType::User(TypeNode::Ty(_), maybe_range)
        //     | VarType::BuiltIn(_, maybe_range) => {
        //         if let Some(range) = maybe_range {
        //             range.simplified_range_max(analyzer)
        //         } else {
        //             Ok(Elem::Dynamic(self.clone()))
        //         }
        //     }
        //     VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
        //         val: concrete_node.underlying(analyzer)?.clone(),
        //         loc: cvar.loc.unwrap_or(Loc::Implicit),
        //     })),
        //     _e => Ok(Elem::Dynamic(self.clone())),
        // }
    }
    fn simplify_minimize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        // let cvar = ContextVarNode::from(self.idx);
        // if cvar.is_symbolic(analyzer)? {
        Ok(Elem::Dynamic(self.clone()))
        // }
        // if !cvar.is_tmp(analyzer)? {
        //     return Ok(Elem::Dynamic(self.clone()))
        // }
        // let cvar = cvar.underlying(analyzer)?;

        // match &cvar.ty {
        //     VarType::User(TypeNode::Contract(_), maybe_range)
        //     | VarType::User(TypeNode::Enum(_), maybe_range)
        //     | VarType::User(TypeNode::Ty(_), maybe_range)
        //     | VarType::BuiltIn(_, maybe_range) => {
        //         if let Some(range) = maybe_range {
        //             range.simplified_range_min(analyzer)
        //         } else {
        //             Ok(Elem::Dynamic(self.clone()))
        //         }
        //     }
        //     VarType::Concrete(concrete_node) => Ok(Elem::Concrete(RangeConcrete {
        //         val: concrete_node.underlying(analyzer)?.clone(),
        //         loc: cvar.loc.unwrap_or(Loc::Implicit),
        //     })),
        //     _e => Ok(Elem::Dynamic(self.clone())),
        // }
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.maximized = Some(MinMaxed::Maximized(Rc::new(self.maximize(g)?)));
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.minimized = Some(MinMaxed::Minimized(Rc::new(self.minimize(g)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
    }
}

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct RangeDyn<T> {
    pub minimized: Option<MinMaxed<T>>,
    pub maximized: Option<MinMaxed<T>>,
    pub len: Elem<T>,
    pub val: BTreeMap<Elem<T>, Elem<T>>,
    pub loc: Loc,
}
impl<T> RangeDyn<T> {
    pub fn set_len(&mut self, new_len: Elem<T>) {
        self.len = new_len;
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.len.contains_node(node_idx)
        // || self.val.iter().any(|(k, v)| k.contains_node(node_idx) || v.contains_node(node_idx))
    }
}

impl RangeElem<Concrete> for RangeDyn<Concrete> {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps: Vec<ContextVarNode> = self.len.dependent_on();
        deps.extend(
            self.val
                .iter()
                .flat_map(|(_, val)| val.dependent_on())
                .collect::<Vec<_>>(),
        );
        deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        self.len.update_deps(mapping);
        self.val
            .iter_mut()
            .for_each(|(_, val)| val.update_deps(mapping));
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.len.filter_recursion(node_idx, new_idx);
        self.val = self
            .val
            .clone()
            .into_iter()
            .map(|(mut k, mut v)| {
                k.filter_recursion(node_idx, new_idx);
                v.filter_recursion(node_idx, new_idx);
                (k, v)
            })
            .collect();
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.clone() {
            return Ok((*cached).clone());
        }

        Ok(Elem::ConcreteDyn(Rc::new(RefCell::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.maximize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.maximize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        }))))
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.clone() {
            return Ok((*cached).clone());
        }

        Ok(Elem::ConcreteDyn(Rc::new(RefCell::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.minimize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.minimize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        }))))
    }

    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::ConcreteDyn(Rc::new(RefCell::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.simplify_maximize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.simplify_maximize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        }))))
    }
    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::ConcreteDyn(Rc::new(RefCell::new(Self {
            minimized: None,
            maximized: None,
            len: self.len.simplify_minimize(analyzer)?,
            val: {
                let mut map = BTreeMap::default();
                for (idx, val) in self.val.clone().into_iter() {
                    map.insert(idx, val.simplify_minimize(analyzer)?);
                }
                map
            },
            loc: self.loc,
        }))))
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.maximized = Some(MinMaxed::Maximized(Rc::new(self.maximize(g)?)));
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.minimized = Some(MinMaxed::Minimized(Rc::new(self.minimize(g)?)));
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.minimized = None;
        self.maximized = None;
    }
}

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeConcrete<T> {
    pub val: T,
    pub loc: Loc,
}

impl From<Concrete> for RangeConcrete<Concrete> {
    fn from(c: Concrete) -> Self {
        Self {
            val: c,
            loc: Loc::Implicit,
        }
    }
}

impl RangeElem<Concrete> for RangeConcrete<Concrete> {
    // fn simplify(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
    // 	Elem::Concrete(self.clone())
    // }

    fn range_eq(&self, other: &Self) -> bool {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(self_val), Some(other_val)) => self_val == other_val,
            _ => match (&self.val, &other.val) {
                (Concrete::Int(_, s), Concrete::Int(_, o)) => s == o,
                (Concrete::DynBytes(s), Concrete::DynBytes(o)) => s == o,
                (Concrete::String(s), Concrete::String(o)) => s == o,
                (Concrete::DynBytes(s), Concrete::String(o)) => s == o.as_bytes(),
                (Concrete::String(s), Concrete::DynBytes(o)) => s.as_bytes() == o,
                (Concrete::Array(a), Concrete::Array(b)) => {
                    if a.len() == b.len() {
                        a.iter().zip(b.iter()).all(|(a, b)| {
                            let a = RangeConcrete {
                                val: a.clone(),
                                loc: self.loc,
                            };

                            let b = RangeConcrete {
                                val: b.clone(),
                                loc: other.loc,
                            };

                            a.range_eq(&b)
                        })
                    } else {
                        false
                    }
                }
                _ => false,
            },
        }
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self.val.into_u256(), other.val.into_u256()) {
            (Some(self_val), Some(other_val)) => Some(self_val.cmp(&other_val)),
            (Some(_), _) => {
                match other.val {
                    Concrete::Int(_, _) => {
                        // if we couldnt convert an int to uint, its negative
                        // so self must be > other
                        Some(std::cmp::Ordering::Greater)
                    }
                    _ => None,
                }
            }
            (_, Some(_)) => {
                match self.val {
                    Concrete::Int(_, _) => {
                        // if we couldnt convert an int to uint, its negative
                        // so self must be < other
                        Some(std::cmp::Ordering::Less)
                    }
                    _ => None,
                }
            }
            _ => {
                match (&self.val, &other.val) {
                    // two negatives
                    (Concrete::Int(_, s), Concrete::Int(_, o)) => Some(s.cmp(o)),
                    (Concrete::DynBytes(b0), Concrete::DynBytes(b1)) => Some(b0.cmp(b1)),
                    _ => None,
                }
            }
        }
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        vec![]
    }
    fn update_deps(&mut self, _mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {}

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx) {}

    fn maximize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.to_owned()))
    }
    fn minimize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.to_owned()))
    }

    fn simplify_maximize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.to_owned()))
    }
    fn simplify_minimize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.to_owned()))
    }

    fn cache_maximize(&mut self, _g: &impl GraphLike) -> Result<(), GraphError> {
        Ok(())
    }

    fn cache_minimize(&mut self, _g: &impl GraphLike) -> Result<(), GraphError> {
        Ok(())
    }
    fn uncache(&mut self) {}
}

#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum MinMaxed<T> {
    Minimized(Rc<Elem<T>>),
    Maximized(Rc<Elem<T>>),
}

/// A range expression composed of other range [`Elem`]
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct RangeExpr<T> {
    pub maximized: Option<MinMaxed<T>>,
    pub minimized: Option<MinMaxed<T>>,
    pub lhs: Rc<RefCell<Elem<T>>>,
    pub op: RangeOp,
    pub rhs: Rc<RefCell<Elem<T>>>,
}

impl<T> RangeExpr<T> {
    /// Creates a new range expression given a left hand side range [`Elem`], a [`RangeOp`], and a a right hand side range [`Elem`].
    pub fn new(lhs: Elem<T>, op: RangeOp, rhs: Elem<T>) -> RangeExpr<T> {
        RangeExpr {
            maximized: None,
            minimized: None,
            lhs: Rc::new(RefCell::new(lhs)),
            op,
            rhs: Rc::new(RefCell::new(rhs)),
        }
    }

    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        self.lhs.borrow().contains_node(node_idx) || self.rhs.borrow().contains_node(node_idx)
    }
}

impl RangeElem<Concrete> for RangeExpr<Concrete> {
    fn range_eq(&self, _other: &Self) -> bool {
        false
    }

    fn range_ord(&self, _other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
        let mut deps = self.lhs.borrow().dependent_on();
        deps.extend(self.rhs.borrow().dependent_on());
        deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        self.lhs.borrow_mut().update_deps(mapping);
        self.rhs.borrow_mut().update_deps(mapping);
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        self.lhs.borrow_mut().filter_recursion(node_idx, new_idx);
        self.rhs.borrow_mut().filter_recursion(node_idx, new_idx);
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Maximized(cached)) = self.maximized.to_owned() {
            Ok((*cached).clone())
        } else {
            self.exec_op(true, analyzer)
        }
    }
    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        if let Some(MinMaxed::Minimized(cached)) = self.minimized.to_owned() {
            Ok((*cached).clone())
        } else {
            self.exec_op(false, analyzer)
        }
    }

    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        self.simplify_exec_op(true, analyzer)
    }
    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        self.simplify_exec_op(false, analyzer)
    }

    fn cache_maximize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.maximized.is_none() {
            self.cache_exec_op(true, g)?;
        }
        Ok(())
    }

    fn cache_minimize(&mut self, g: &impl GraphLike) -> Result<(), GraphError> {
        if self.minimized.is_none() {
            self.cache_exec_op(false, g)?;
        }
        Ok(())
    }

    fn uncache(&mut self) {
        self.uncache_exec();
    }
}

/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum Elem<T> {
    /// A range element that is a reference to another node
    Dynamic(Dynamic),
    /// A concrete range element of type `T`. e.g.: some number like `10`
    ConcreteDyn(Rc<RefCell<RangeDyn<T>>>),
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
            Elem::Dynamic(Dynamic { idx, .. }) => write!(f, "idx_{}", idx.index()),
            Elem::ConcreteDyn(..) => write!(f, "range_elem"),
            Elem::Concrete(RangeConcrete { val, .. }) => {
                write!(f, "{}", val.as_string())
            }
            Elem::Expr(RangeExpr { lhs, op, rhs, .. }) => {
                write!(f, "({} {} {})", op.to_string(), lhs.borrow(), rhs.borrow())
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
        Elem::Dynamic(Dynamic::new(c.into()))
    }
}

impl From<NodeIdx> for Elem<Concrete> {
    fn from(idx: NodeIdx) -> Self {
        Elem::Dynamic(Dynamic::new(idx))
    }
}

impl<T> Elem<T> {
    pub fn contains_node(&self, node_idx: NodeIdx) -> bool {
        match self {
            Self::Dynamic(d) => d.idx == node_idx,
            Self::Concrete(_) => false,
            Self::Expr(expr) => expr.contains_node(node_idx),
            Self::ConcreteDyn(d) => d.borrow().contains_node(node_idx),
            Self::Null => false,
        }
    }

    pub fn dyn_map(&self) -> Option<Rc<RefCell<RangeDyn<T>>>> {
        match self {
            Self::ConcreteDyn(dyn_range) => Some(Rc::clone(dyn_range)),
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

impl<T> From<Dynamic> for Elem<T> {
    fn from(dy: Dynamic) -> Self {
        Elem::Dynamic(dy)
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
            Self::Dynamic(Dynamic { idx, .. }) => Some(*idx),
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
            Elem::Dynamic(dy) => {
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
            Elem::ConcreteDyn(a) => Some(a.borrow().clone()),
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
            Self::Dynamic(d) => d.dependent_on(),
            Self::Concrete(_) => vec![],
            Self::Expr(expr) => expr.dependent_on(),
            Self::ConcreteDyn(d) => d.borrow().dependent_on(),
            Self::Null => vec![],
        }
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
        match self {
            Self::Dynamic(d) => d.update_deps(mapping),
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.update_deps(mapping),
            Self::ConcreteDyn(d) => d.borrow_mut().update_deps(mapping),
            Self::Null => {}
        }
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, new_idx: NodeIdx) {
        match self {
            Self::Dynamic(ref mut d) => {
                if d.idx == node_idx {
                    d.idx = new_idx
                }
            }
            Self::Concrete(_) => {}
            Self::Expr(expr) => expr.filter_recursion(node_idx, new_idx),
            Self::ConcreteDyn(d) => d.borrow_mut().filter_recursion(node_idx, new_idx),
            Self::Null => {}
        }
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Dynamic(dy) => dy.maximize(analyzer)?,
            Concrete(inner) => inner.maximize(analyzer)?,
            ConcreteDyn(inner) => inner.borrow().maximize(analyzer)?,
            Expr(expr) => expr.maximize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Dynamic(dy) => dy.minimize(analyzer)?,
            Concrete(inner) => inner.minimize(analyzer)?,
            ConcreteDyn(inner) => inner.borrow().minimize(analyzer)?,
            Expr(expr) => expr.minimize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Dynamic(dy) => dy.simplify_maximize(analyzer)?,
            Concrete(inner) => inner.simplify_maximize(analyzer)?,
            ConcreteDyn(inner) => inner.borrow().simplify_maximize(analyzer)?,
            Expr(expr) => expr.simplify_maximize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        use Elem::*;
        let res = match self {
            Dynamic(dy) => dy.simplify_minimize(analyzer)?,
            Concrete(inner) => inner.simplify_minimize(analyzer)?,
            ConcreteDyn(inner) => inner.borrow().simplify_minimize(analyzer)?,
            Expr(expr) => expr.simplify_minimize(analyzer)?,
            Null => Elem::Null,
        };
        Ok(res)
    }

    fn cache_maximize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Dynamic(dy) => dy.cache_maximize(analyzer),
            Concrete(inner) => inner.cache_maximize(analyzer),
            ConcreteDyn(inner) => inner.borrow_mut().cache_maximize(analyzer),
            Expr(expr) => expr.cache_maximize(analyzer),
            Null => Ok(()),
        }
    }

    fn cache_minimize(&mut self, analyzer: &impl GraphLike) -> Result<(), GraphError> {
        use Elem::*;
        match self {
            Dynamic(dy) => dy.cache_minimize(analyzer),
            Concrete(inner) => inner.cache_minimize(analyzer),
            ConcreteDyn(inner) => inner.borrow_mut().cache_minimize(analyzer),
            Expr(expr) => expr.cache_minimize(analyzer),
            Null => Ok(()),
        }
    }
    fn uncache(&mut self) {
        use Elem::*;
        match self {
            Dynamic(dy) => dy.uncache(),
            Concrete(inner) => inner.uncache(),
            ConcreteDyn(inner) => inner.borrow_mut().uncache(),
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
        analyzer: &impl GraphLike,
    ) -> Result<(Elem<T>, Elem<T>, Elem<T>, Elem<T>), GraphError>;

    fn uncache_exec(&mut self);

    fn simplify_exec_op(
        &self,
        maximize: bool,
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

impl ExecOp<Concrete> for RangeExpr<Concrete> {
    fn cache_exec_op(
        &mut self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<(), GraphError> {
        self.lhs.borrow_mut().cache_minimize(analyzer)?;
        self.lhs.borrow_mut().cache_maximize(analyzer)?;
        self.rhs.borrow_mut().cache_minimize(analyzer)?;
        self.rhs.borrow_mut().cache_maximize(analyzer)?;
        let res = self.exec_op(maximize, analyzer)?;
        if maximize {
            self.maximized = Some(MinMaxed::Maximized(Rc::new(res)));
        } else {
            self.minimized = Some(MinMaxed::Minimized(Rc::new(res)));
        }
        Ok(())
    }

    fn uncache_exec(&mut self) {
        self.lhs.borrow_mut().uncache();
        self.rhs.borrow_mut().uncache();
    }

    fn simplify_exec_op(
        &self,
        maximize: bool,
        analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        let parts = self.simplify_spread(analyzer)?;
        self.exec(parts, maximize)
    }

    fn spread(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<
        (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        GraphError,
    > {
        let lhs_min = self.lhs.borrow().minimize(analyzer)?;
        let lhs_max = self.lhs.borrow().maximize(analyzer)?;
        let rhs_min = self.rhs.borrow().minimize(analyzer)?;
        let rhs_max = self.rhs.borrow().maximize(analyzer)?;
        Ok((lhs_min, lhs_max, rhs_min, rhs_max))
    }

    fn simplify_spread(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<
        (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        GraphError,
    > {
        let lhs_min = self.lhs.borrow().simplify_minimize(analyzer)?;
        let lhs_max = self.lhs.borrow().simplify_maximize(analyzer)?;
        let rhs_min = self.rhs.borrow().simplify_minimize(analyzer)?;
        let rhs_max = self.rhs.borrow().simplify_maximize(analyzer)?;
        Ok((lhs_min, lhs_max, rhs_min, rhs_max))
    }

    fn exec(
        &self,
        (lhs_min, lhs_max, rhs_min, rhs_max): (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        maximize: bool,
    ) -> Result<Elem<Concrete>, GraphError> {
        tracing::trace!(
            "executing: {} {} {}, lhs_min: {}, lhs_max: {}, rhs_min: {}, rhs_max: {}",
            self.lhs.borrow(),
            self.op.to_string(),
            self.rhs.borrow(),
            lhs_min,
            lhs_max,
            rhs_min,
            rhs_max
        );

        let lhs_min_neg = lhs_min.pre_evaled_is_negative();
        let lhs_max_neg = lhs_max.pre_evaled_is_negative();
        let rhs_min_neg = rhs_min.pre_evaled_is_negative();
        let rhs_max_neg = rhs_max.pre_evaled_is_negative();

        let res = match self.op {
            RangeOp::Add(unchecked) => {
                if unchecked {
                    let candidates = vec![
                        lhs_min.range_wrapping_add(&rhs_min),
                        lhs_min.range_wrapping_add(&rhs_max),
                        lhs_max.range_wrapping_add(&rhs_min),
                        lhs_max.range_wrapping_add(&rhs_max),
                        lhs_max.range_add(&rhs_max),
                        lhs_min.range_add(&rhs_min),
                    ];
                    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                    candidates.sort_by(|a, b| match a.range_ord(b) {
                        Some(r) => r,
                        _ => std::cmp::Ordering::Less,
                    });

                    if candidates.is_empty() {
                        return Ok(Elem::Expr(self.to_owned()));
                    }

                    if maximize {
                        candidates.remove(candidates.len() - 1)
                    } else {
                        candidates.remove(0)
                    }
                } else if maximize {
                    // if we are maximizing, the largest value will always just be the the largest value + the largest value
                    lhs_max
                        .range_add(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    lhs_min
                        .range_add(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Sub(unchecked) => {
                if unchecked {
                    let candidates = vec![
                        lhs_min.range_wrapping_sub(&rhs_min),
                        lhs_min.range_wrapping_sub(&rhs_max),
                        lhs_max.range_wrapping_sub(&rhs_min),
                        lhs_max.range_wrapping_sub(&rhs_max),
                    ];
                    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                    candidates.sort_by(|a, b| match a.range_ord(b) {
                        Some(r) => r,
                        _ => std::cmp::Ordering::Less,
                    });

                    if candidates.is_empty() {
                        return Ok(Elem::Expr(self.to_owned()));
                    }

                    if maximize {
                        candidates.remove(candidates.len() - 1)
                    } else {
                        candidates.remove(0)
                    }
                } else if maximize {
                    // if we are maximizing, the largest value will always just be the the largest value - the smallest value
                    lhs_max
                        .range_sub(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    // if we are minimizing, the smallest value will always be smallest value - largest value
                    lhs_min
                        .range_sub(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Mul(unchecked) => {
                if unchecked {
                    let candidates = vec![
                        lhs_min.range_wrapping_mul(&rhs_min),
                        lhs_min.range_wrapping_mul(&rhs_max),
                        lhs_max.range_wrapping_mul(&rhs_min),
                        lhs_max.range_wrapping_mul(&rhs_max),
                    ];
                    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                    candidates.sort_by(|a, b| match a.range_ord(b) {
                        Some(r) => r,
                        _ => std::cmp::Ordering::Less,
                    });

                    if candidates.is_empty() {
                        return Ok(Elem::Expr(self.to_owned()));
                    }

                    if maximize {
                        candidates.remove(candidates.len() - 1)
                    } else {
                        candidates.remove(0)
                    }
                } else if maximize {
                    // if we are maximizing, and both mins are negative and both maxes are positive,
                    // we dont know which will be larger of the two (i.e. -1*2**255 * -1*2**255 > 100*100)
                    match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                        (true, true, true, true) => {
                            // all negative, will be min * min because those are furthest from 0 resulting in the
                            // largest positive value
                            lhs_min
                                .range_mul(&rhs_min)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (true, false, true, false) => {
                            // we dont know if lhs_max * rhs_min is larger or lhs_min * rhs_max is smaller
                            match (lhs_min.range_mul(&rhs_min), lhs_max.range_mul(&rhs_max)) {
                                (Some(min_expr), Some(max_expr)) => {
                                    match min_expr.range_ord(&max_expr) {
                                        Some(std::cmp::Ordering::Less) => max_expr,
                                        Some(std::cmp::Ordering::Greater) => min_expr,
                                        _ => max_expr,
                                    }
                                }
                                (None, Some(max_expr)) => max_expr,
                                (Some(min_expr), None) => min_expr,
                                (None, None) => Elem::Expr(self.to_owned()),
                            }
                        }
                        (_, false, _, false) => {
                            // rhs_max is positive, lhs_max is positive, guaranteed to be largest max value
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (false, false, true, true) => {
                            // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                            lhs_min
                                .range_mul(&rhs_max)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (true, true, false, false) => {
                            // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                            lhs_max
                                .range_mul(&rhs_min)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (true, _, true, _) => lhs_min
                            .range_mul(&rhs_min)
                            .unwrap_or(Elem::Expr(self.to_owned())),
                        (false, true, _, _) | (_, _, false, true) => {
                            panic!("unsatisfiable range")
                        }
                    }
                } else {
                    match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                        (false, false, false, false) => {
                            // rhs_min is positive, lhs_min is positive, guaranteed to be smallest max value
                            lhs_min
                                .range_mul(&rhs_min)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (true, true, true, true) => {
                            // all negative, will be max * max because those are closest to 0 resulting in the
                            // smallest positive value
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (true, false, true, false) => {
                            // we dont know if lhs_max * rhs_min is smaller or lhs_min * rhs_max is smaller
                            match (lhs_max.range_mul(&rhs_min), lhs_min.range_mul(&rhs_max)) {
                                (Some(min_expr), Some(max_expr)) => {
                                    match min_expr.range_ord(&max_expr) {
                                        Some(std::cmp::Ordering::Less) => min_expr,
                                        Some(std::cmp::Ordering::Greater) => max_expr,
                                        _ => min_expr,
                                    }
                                }
                                (None, Some(max_expr)) => max_expr,
                                (Some(min_expr), None) => min_expr,
                                (None, None) => Elem::Expr(self.to_owned()),
                            }
                        }
                        (true, _, _, false) => {
                            // rhs_max is positive, lhs_min is negative, guaranteed to be largest min value
                            lhs_min
                                .range_mul(&rhs_max)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (_, false, _, true) => {
                            // just lhs has a positive value, most negative will be lhs_max, rhs_max
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or(Elem::Expr(self.to_owned()))
                        }
                        (false, false, true, false) => lhs_max
                            .range_mul(&rhs_min)
                            .unwrap_or(Elem::Expr(self.to_owned())),
                        (false, true, _, _) | (_, _, false, true) => {
                            panic!("unsatisfiable range")
                        }
                    }
                }
            }
            RangeOp::Div(_unchecked) => {
                let mut candidates = vec![
                    lhs_min.range_div(&rhs_min),
                    lhs_min.range_div(&rhs_max),
                    lhs_max.range_div(&rhs_min),
                    lhs_max.range_div(&rhs_max),
                ];

                let one = Elem::from(Concrete::from(U256::from(1)));
                let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

                let min_contains = matches!(
                    rhs_min.range_ord(&one),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&one),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_div(&one));
                    candidates.push(lhs_max.range_div(&one));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_div(&negative_one));
                    candidates.push(lhs_max.range_div(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
                // if maximize {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(true, false, true, false) => {
                // 			// we dont know if lhs_min / rhs_min is larger or lhs_max / rhs_max is larger
                // 			match (lhs_min.range_div(&rhs_min), lhs_max.range_div(&rhs_max)) {
                // 				(Some(min_expr), Some(max_expr)) => {
                // 					match min_expr.range_ord(&max_expr) {
                // 						Some(std::cmp::Ordering::Less) => {
                // 							max_expr
                // 						}
                // 						Some(std::cmp::Ordering::Greater) => {
                // 							min_expr
                // 						}
                // 						_ => {
                // 							max_expr
                // 						}
                // 					}
                // 				}
                // 				(None, Some(max_expr)) => {
                // 					max_expr
                // 				}
                // 				(Some(min_expr), None) => {
                // 					min_expr
                // 				}
                // 				(None, None) => Elem::Expr(self.clone())
                // 			}
                // 		}
                // 		(false, false, true, true) => {
                // 			// since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                // 			lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, true, false, false) => {
                // 			// since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                // 			lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(_, false, false, _) => {
                // 			// lhs is positive, rhs min is positive, guaranteed to give largest
                // 			lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(_, false, true, false) => {
                // 			// lhs_max is positive and rhs_max is positive, guaranteed to be lhs_max and rhs_max
                // 			lhs_max.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, _, true, _) => {
                // 			// at this point, its either all trues, or a single false
                // 			// given that, to maximize, the only way to get a positive value is to use the most negative values
                // 			lhs_min.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // } else {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(false, false, false, false) => {
                // 			// smallest number will be lhs_min / rhs_min since both are positive
                // 			lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, true, true, true) => {
                // 			// smallest number will be lhs_max / rhs_min since both are negative
                // 			lhs_max.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, true, true, false) => {
                // 			// The way to maintain most negative value is lhs_min / rhs_max, all others would go
                // 			// positive or guaranteed to be closer to 0
                // 			lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, false, true, false) => {
                // 			// we dont know if lhs_min / rhs_max is larger or lhs_max / rhs_min is larger
                // 			match (lhs_min.range_div(&rhs_max), lhs_max.range_div(&rhs_min)) {
                // 				(Some(min_expr), Some(max_expr)) => {
                // 					match min_expr.range_ord(&max_expr) {
                // 						Some(std::cmp::Ordering::Less) => {
                // 							min_expr
                // 						}
                // 						Some(std::cmp::Ordering::Greater) => {
                // 							max_expr
                // 						}
                // 						_ => {
                // 							min_expr
                // 						}
                // 					}
                // 				}
                // 				(None, Some(max_expr)) => {
                // 					max_expr
                // 				}
                // 				(Some(min_expr), None) => {
                // 					min_expr
                // 				}
                // 				(None, None) => Elem::Expr(self.clone())
                // 			}
                // 		}
                // 		(_, false, true, _) => {
                // 			// We are going negative here, so it will be most positive / least negative
                // 			lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, _, false, _) => {
                // 			// We are going negative here, so it will be most negative / least positive
                // 			lhs_min.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // }
            }
            // RangeOp::Mod => {
            //     lhs.range_mod(&rhs).unwrap_or(Elem::Expr(self.clone()))
            // }
            RangeOp::Min => {
                let candidates = vec![
                    lhs_min.range_min(&rhs_min),
                    lhs_min.range_min(&rhs_max),
                    lhs_max.range_min(&rhs_min),
                    lhs_max.range_min(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
                // if maximize {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(true, _, true, _) | (false, _, false, _) => {
                // 			// counter-intuitively, we want the maximum value from a call to minimum
                // 			// this is due to the symbolic nature of the evaluation. We are still
                // 			// using the minimum values but getting the larger of the minimum
                // 			lhs_min.range_max(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, _, false, false) => {
                // 			rhs_min //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, false, true, _) => {
                // 			lhs_min //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // } else {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(true, _, true, _) | (false, _, false, _) => {
                // 			lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, _, false, false) => {
                // 			lhs_min //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, false, true, _) => {
                // 			rhs_min //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // }
            }
            RangeOp::Max => {
                let candidates = vec![
                    lhs_min.range_max(&rhs_min),
                    lhs_min.range_max(&rhs_max),
                    lhs_max.range_max(&rhs_min),
                    lhs_max.range_max(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
                // if maximize {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(true, _, true, _) | (false, _, false, _) => {
                // 			lhs_max.range_max(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, _, false, false) => {
                // 			rhs_max //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, false, true, _) => {
                // 			lhs_max //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // } else {
                // 	match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                // 		(_, true, _, true) | (_, false, _, false) => {
                // 			// counter-intuitively, we want the minimum value from a call to maximum
                // 			// this is due to the symbolic nature of the evaluation. We are still
                // 			// using the maximum values but getting the smaller of the maximum
                // 			lhs_max.range_min(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(_, false, true, true) => {
                // 			lhs_max //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(true, true, _, false) => {
                // 			rhs_max //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                // 		}
                // 		(false, true, _, _) | (_, _, false, true)=> {
                // 			panic!("unsatisfiable range")
                // 		}
                // 	}
                // }
            }
            RangeOp::Gt => {
                if maximize {
                    lhs_max
                        .range_gt(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    lhs_min
                        .range_gt(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Lt => {
                if maximize {
                    lhs_min
                        .range_lt(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    lhs_max
                        .range_lt(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Gte => {
                if maximize {
                    lhs_max
                        .range_gte(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    lhs_min
                        .range_gte(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Lte => {
                if maximize {
                    lhs_min
                        .range_lte(&rhs_max)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                } else {
                    lhs_max
                        .range_lte(&rhs_min)
                        .unwrap_or(Elem::Expr(self.to_owned()))
                }
            }
            RangeOp::Eq => {
                let loc = if let Some(c) = lhs_min.maybe_concrete() {
                    c.loc
                } else if let Some(c) = lhs_max.maybe_concrete() {
                    c.loc
                } else if let Some(c) = rhs_min.maybe_concrete() {
                    c.loc
                } else if let Some(c) = rhs_max.maybe_concrete() {
                    c.loc
                } else {
                    Loc::Implicit
                };

                if maximize {
                    // check for any overlap
                    let lhs_max_rhs_min_ord = lhs_max.range_ord(&rhs_min);
                    let lhs_min_rhs_max_ord = lhs_min.range_ord(&rhs_max);

                    // if lhs max is less than the rhs min, it has to be false
                    if matches!(lhs_max_rhs_min_ord, Some(std::cmp::Ordering::Less)) {
                        return Ok(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc,
                        }));
                    }

                    // if lhs min is greater than the rhs max, it has to be false
                    if matches!(lhs_min_rhs_max_ord, Some(std::cmp::Ordering::Greater)) {
                        return Ok(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc,
                        }));
                    }

                    // lhs_max >= rhs_min
                    // lhs_min <= rhs_max
                    // therefore its possible to set some value to true here
                    if lhs_max_rhs_min_ord.is_some() && lhs_min_rhs_max_ord.is_some() {
                        Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc,
                        })
                    } else {
                        Elem::Expr(self.to_owned())
                    }
                } else {
                    // check if either lhs element is *not* contained by rhs
                    match (
                        // check if lhs is constant
                        lhs_min.range_ord(&lhs_max),
                        // check if rhs is constant
                        rhs_min.range_ord(&rhs_max),
                        // check if lhs is equal to rhs
                        lhs_min.range_ord(&rhs_min),
                    ) {
                        (
                            Some(std::cmp::Ordering::Equal),
                            Some(std::cmp::Ordering::Equal),
                            Some(std::cmp::Ordering::Equal),
                        ) => Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc,
                        }),
                        // if any of those are not equal, we can construct
                        // an element that is true
                        _ => Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc,
                        }),
                    }
                }
            }
            RangeOp::Neq => {
                let loc = if let Some(c) = lhs_min.maybe_concrete() {
                    c.loc
                } else if let Some(c) = lhs_max.maybe_concrete() {
                    c.loc
                } else if let Some(c) = rhs_min.maybe_concrete() {
                    c.loc
                } else if let Some(c) = rhs_max.maybe_concrete() {
                    c.loc
                } else {
                    Loc::Implicit
                };
                if maximize {
                    // check if either lhs element is *not* contained by rhs
                    match (
                        // check if lhs is constant
                        lhs_min.range_ord(&lhs_max),
                        // check if rhs is constant
                        rhs_min.range_ord(&rhs_max),
                        // check if lhs is equal to rhs
                        lhs_min.range_ord(&rhs_min),
                    ) {
                        (
                            Some(std::cmp::Ordering::Equal),
                            Some(std::cmp::Ordering::Equal),
                            Some(std::cmp::Ordering::Equal),
                        ) => Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc,
                        }),
                        // if any of those are not equal, we can construct
                        // an element that is true
                        _ => Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc,
                        }),
                    }
                } else {
                    // if they are constants and equal, we can stop here
                    //   (rhs min == rhs max) == (lhs min == lhs max )
                    if let (
                        Some(std::cmp::Ordering::Equal),
                        Some(std::cmp::Ordering::Equal),
                        Some(std::cmp::Ordering::Equal),
                    ) = (
                        // check if lhs is constant
                        lhs_min.range_ord(&lhs_max),
                        // check if rhs is constant
                        rhs_min.range_ord(&rhs_max),
                        // check if lhs is equal to rhs
                        lhs_min.range_ord(&rhs_min),
                    ) {
                        return Ok(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(false),
                            loc,
                        }));
                    }

                    // they aren't constants, check if there is any overlap
                    match (
                        // check if lhs minimum is contained within the right hand side
                        // this means the values could be equal
                        // effectively:
                        //   rhs min <= lhs min <= rhs max
                        lhs_min.range_ord(&rhs_min),
                        lhs_min.range_ord(&rhs_max),
                    ) {
                        (_, Some(std::cmp::Ordering::Equal))
                        | (Some(std::cmp::Ordering::Equal), _)
                        | (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less)) => {
                            return Ok(Elem::Concrete(RangeConcrete {
                                val: Concrete::Bool(false),
                                loc,
                            }))
                        }
                        _ => {}
                    }

                    match (
                        // check if the lhs maximum is contained within the right hand side
                        // effectively:
                        //   rhs min <= lhs max <= rhs max
                        lhs_max.range_ord(&rhs_min),
                        lhs_max.range_ord(&rhs_max),
                    ) {
                        (_, Some(std::cmp::Ordering::Equal))
                        | (Some(std::cmp::Ordering::Equal), _)
                        | (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less)) => {
                            return Ok(Elem::Concrete(RangeConcrete {
                                val: Concrete::Bool(false),
                                loc,
                            }))
                        }
                        _ => {}
                    }

                    Elem::Expr(self.to_owned())
                }
            }
            RangeOp::Shl => {
                let candidates = vec![
                    lhs_min.range_shl(&rhs_min),
                    lhs_min.range_shl(&rhs_max),
                    lhs_max.range_shl(&rhs_min),
                    lhs_max.range_shl(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Shr => {
                let candidates = vec![
                    lhs_min.range_shr(&rhs_min),
                    lhs_min.range_shr(&rhs_max),
                    lhs_max.range_shr(&rhs_min),
                    lhs_max.range_shr(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::And => {
                let candidates = vec![
                    lhs_min.range_and(&rhs_min),
                    lhs_min.range_and(&rhs_max),
                    lhs_max.range_and(&rhs_min),
                    lhs_max.range_and(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Or => {
                let candidates = vec![
                    lhs_min.range_or(&rhs_min),
                    lhs_min.range_or(&rhs_max),
                    lhs_max.range_or(&rhs_min),
                    lhs_max.range_or(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Not => {
                assert!(matches!(rhs_min, Elem::Null) && matches!(rhs_max, Elem::Null));
                let candidates = vec![lhs_min.range_not(), lhs_min.range_not()];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Cast => {
                // the weird thing about cast is that we really dont know until after the cast due to sizing things
                // so we should just try them all then compare
                let candidates = vec![
                    lhs_min.range_cast(&rhs_min),
                    lhs_min.range_cast(&rhs_max),
                    lhs_max.range_cast(&rhs_min),
                    lhs_max.range_cast(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Exp => {
                // TODO: improve with smarter stuff
                let candidates = vec![
                    lhs_min.range_exp(&rhs_min),
                    lhs_min.range_exp(&rhs_max),
                    lhs_max.range_exp(&rhs_min),
                    lhs_max.range_exp(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::BitAnd => {
                let mut candidates = vec![
                    lhs_min.range_bit_and(&rhs_min),
                    lhs_min.range_bit_and(&rhs_max),
                    lhs_max.range_bit_and(&rhs_min),
                    lhs_max.range_bit_and(&rhs_max),
                ];

                let zero = Elem::from(Concrete::from(U256::from(0)));
                let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

                let min_contains = matches!(
                    rhs_min.range_ord(&zero),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_and(&zero));
                    candidates.push(lhs_max.range_bit_and(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_and(&negative_one));
                    candidates.push(lhs_max.range_bit_and(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::BitOr => {
                let mut candidates = vec![
                    lhs_min.range_bit_or(&rhs_min),
                    lhs_min.range_bit_or(&rhs_max),
                    lhs_max.range_bit_or(&rhs_min),
                    lhs_max.range_bit_or(&rhs_max),
                ];

                let zero = Elem::from(Concrete::from(U256::from(0)));
                let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

                let min_contains = matches!(
                    rhs_min.range_ord(&zero),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_or(&zero));
                    candidates.push(lhs_max.range_bit_or(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_or(&negative_one));
                    candidates.push(lhs_max.range_bit_or(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::BitXor => {
                let mut candidates = vec![
                    lhs_min.range_bit_xor(&rhs_min),
                    lhs_min.range_bit_xor(&rhs_max),
                    lhs_max.range_bit_xor(&rhs_min),
                    lhs_max.range_bit_xor(&rhs_max),
                ];

                let zero = Elem::from(Concrete::from(U256::from(0)));
                let negative_one = Elem::from(Concrete::from(I256::from(-1i32)));

                let min_contains = matches!(
                    rhs_min.range_ord(&zero),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    // if the rhs contains zero, in xor, thats just itself
                    candidates.push(lhs_max.range_bit_xor(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_xor(&negative_one));
                    candidates.push(lhs_max.range_bit_xor(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::BitNot => {
                let mut candidates = vec![lhs_min.range_bit_not(), lhs_max.range_bit_not()];

                let zero = Elem::from(Concrete::from(U256::from(0)));

                let min_contains = matches!(
                    lhs_min.range_ord(&zero),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    lhs_max.range_ord(&zero),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    match lhs_min {
                        Elem::Concrete(
                            r @ RangeConcrete {
                                val: Concrete::Uint(..),
                                ..
                            },
                        ) => candidates.push(Some(Elem::from(Concrete::max(&r.val).unwrap()))),
                        Elem::Concrete(
                            r @ RangeConcrete {
                                val: Concrete::Int(..),
                                ..
                            },
                        ) => candidates.push(Some(Elem::from(Concrete::min(&r.val).unwrap()))),
                        _ => {}
                    }
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            RangeOp::Concat => {
                // TODO: improve with smarter stuff
                let candidates = vec![
                    lhs_min.range_concat(&rhs_min),
                    lhs_min.range_concat(&rhs_max),
                    lhs_max.range_concat(&rhs_min),
                    lhs_max.range_concat(&rhs_max),
                ];
                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(Elem::Expr(self.to_owned()));
                }

                if maximize {
                    candidates.remove(candidates.len() - 1)
                } else {
                    candidates.remove(0)
                }
            }
            _ => Elem::Expr(self.to_owned()),
        };
        Ok(res)
    }
}
