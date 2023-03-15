use std::collections::BTreeMap;
use crate::range::Range;
use std::ops::*;
use crate::range::range_ops::*;
use crate::context::ContextVarNode;
use crate::{nodes::VarType};
use crate::{Concrete, NodeIdx};
use crate::range::{elem::RangeOp, *};
use solang_parser::pt::Loc;

/// A dynamic range element value
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Dynamic {
	/// Index of the node that is referenced
	pub idx: NodeIdx,
	/// Sourcecode location
	pub loc: Loc,
}

impl Dynamic {
	pub fn new(idx: NodeIdx, loc: Loc) -> Self {
		Self { idx, loc }
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

	fn filter_recursion(&mut self, _: NodeIdx, _: Elem<Concrete>) {}

	fn maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
        let cvar = ContextVarNode::from(self.idx).underlying(analyzer);
        match &cvar.ty {
            VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_max(analyzer)
                } else {
                    Elem::Dynamic(*self)
                }
            }
            VarType::Concrete(concrete_node) => {
            	Elem::Concrete(
            		RangeConcrete {
            			val: concrete_node.underlying(analyzer).clone(),
            			loc: cvar.loc.unwrap_or(Loc::Implicit)
            		}
            	)
            },
            e => {println!("dynamic {:?}", e); Elem::Dynamic(*self)},
        }
	}

	fn minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let cvar = ContextVarNode::from(self.idx).underlying(analyzer);
        match &cvar.ty {
            VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    range.evaled_range_min(analyzer)
                } else {
                    Elem::Dynamic(*self)
                }
            }
            VarType::Concrete(concrete_node) => {
            	Elem::Concrete(
            		RangeConcrete {
            			val: concrete_node.underlying(analyzer).clone(),
            			loc: cvar.loc.unwrap_or(Loc::Implicit)
            		}
            	)
            },
            e => {println!("dynamic {:?}", e); Elem::Dynamic(*self)},
        }
	}

	fn simplify_maximize(&self, _: &impl GraphLike) -> Elem<Concrete> {
		Elem::Dynamic(*self)
	}
	fn simplify_minimize(&self, _: &impl GraphLike) -> Elem<Concrete> {
		Elem::Dynamic(*self)
	}
}

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeDyn<T> {
	pub len: Elem<T>,
	pub val: BTreeMap<Elem<T>, Elem<T>>,
	pub loc: Loc,
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
		deps.extend(self.val.iter().flat_map(|(_, val)| val.dependent_on()).collect::<Vec<_>>());
		deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
    	self.len.update_deps(mapping);
		self.val.iter_mut().for_each(|(_, val)| val.update_deps(mapping));
    }

	fn filter_recursion(&mut self, _: NodeIdx, _: Elem<Concrete>) {}

	fn maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::ConcreteDyn(Box::new(Self {
			len: self.len.maximize(analyzer),
			val: self.val.clone().into_iter().map(|(idx, val)| (idx, val.maximize(analyzer))).collect(),
			loc: self.loc
		}))
	}

	fn minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::ConcreteDyn(Box::new(Self {
			len: self.len.minimize(analyzer),
			val: self.val.clone().into_iter().map(|(idx, val)| (idx, val.minimize(analyzer))).collect(),
			loc: self.loc
		}))
	}

	fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::ConcreteDyn(Box::new(Self {
			len: self.len.simplify_maximize(analyzer),
			val: self.val.clone().into_iter().map(|(idx, val)| (idx, val.simplify_maximize(analyzer))).collect(),
			loc: self.loc
		}))
	}
	fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::ConcreteDyn(Box::new(Self {
			len: self.len.simplify_minimize(analyzer),
			val: self.val.clone().into_iter().map(|(idx, val)| (idx, val.simplify_minimize(analyzer))).collect(),
			loc: self.loc
		}))
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
    		_ => {
    			match (&self.val, &other.val) {
    				(Concrete::DynBytes(s), Concrete::DynBytes(o)) => s == o,
    				(Concrete::String(s), Concrete::String(o)) => s == o,
    				(Concrete::DynBytes(s), Concrete::String(o)) => s == o.as_bytes(),
    				(Concrete::String(s), Concrete::DynBytes(o)) => s.as_bytes() == o,
    				(Concrete::Array(a), Concrete::Array(b)) => {
    					if a.len() == b.len() {
	    					a.iter().zip(b.iter()).all(|(a, b)| {
	    						let a = RangeConcrete {
	    							val: a.clone(),
	    							loc: self.loc
	    						};

	    						let b = RangeConcrete {
	    							val: b.clone(),
	    							loc: other.loc
	    						};
	    						
	    						a.range_eq(&b)
	    					})
	    				} else {
	    					false
	    				}
    				}
    				_ => false
    			}
    		}
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
    				_ => None
    			}
    		}
    		(_, Some(_)) => {
    			match self.val {
    				Concrete::Int(_, _) => {
    					// if we couldnt convert an int to uint, its negative
    					// so self must be < other
    					Some(std::cmp::Ordering::Less)
    				}
    				_ => None
    			}
    		}
    		_ => {
    			match (&self.val, &other.val) {
    				// two negatives
    				(Concrete::Int(_, s), Concrete::Int(_, o)) => {
    					Some(s.cmp(o))
    				},
    				_ => None
    			}
    		}
    	}
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
    	vec![]
    }
    fn update_deps(&mut self, _mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {}

    fn filter_recursion(&mut self, _: NodeIdx, _: Elem<Concrete>) {}

    fn maximize(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}
	fn minimize(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}

	fn simplify_maximize(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}
	fn simplify_minimize(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}
}

/// A range expression composed of other range [`Elem`]
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeExpr<T> {
	pub lhs: Box<Elem<T>>,
	pub op: RangeOp,
	pub rhs: Box<Elem<T>>,
}

impl<T> RangeExpr<T> {
	/// Creates a new range expression given a left hand side range [`Elem`], a [`RangeOp`], and a a right hand side range [`Elem`].
	pub fn new(lhs: Elem<T>, op: RangeOp, rhs: Elem<T>) -> RangeExpr<T> {
		RangeExpr {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        }
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
    	let mut deps = self.lhs.dependent_on();
    	deps.extend(self.rhs.dependent_on());
    	deps
    }

    fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
    	self.lhs.update_deps(mapping);
    	self.rhs.update_deps(mapping);
    }

    fn filter_recursion(&mut self, node_idx: NodeIdx, old: Elem<Concrete>) {
    	self.lhs.filter_recursion(node_idx, old.clone());
    	self.rhs.filter_recursion(node_idx, old);
    }

    fn maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
    	self.exec_op(true, analyzer)
		// Elem::Dynamic(self.clone())
	}
	fn minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		// Elem::Dynamic(self.clone())
		self.exec_op(false, analyzer)
	}

	fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		self.simplify_exec_op(true, analyzer)
	}
	fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		self.simplify_exec_op(false, analyzer)
	}
}

/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Elem<T> {
	/// A range element that is a reference to another node
	Dynamic(Dynamic),
	/// A concrete range element of type `T`. e.g.: some number like `10`
	ConcreteDyn(Box<RangeDyn<T>>),
	/// A concrete range element of type `T`. e.g.: some number like `10`
	Concrete(RangeConcrete<T>),
	/// A range element that is an expression composed of other range elements
	Expr(RangeExpr<T>),
	/// A null range element useful in range expressions that dont have a rhs
	Null,
}

impl From<Concrete> for Elem<Concrete> {
	fn from(c: Concrete) -> Self {
		Elem::Concrete(RangeConcrete { val: c, loc: Loc::Implicit })
	}
}

impl<T> Elem<T> {
	/// Creates a new range element that is a cast from one type to another
	pub fn cast(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Cast,
            rhs: Box::new(other),
        };
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the minimum of two range elements
	pub fn min(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Min,
            rhs: Box::new(other),
        };
        Elem::Expr(expr)
    }

    /// Creates a new range element that is the maximum of two range elements
    pub fn max(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Max,
            rhs: Box::new(other),
        };
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of equality of two range elements
    pub fn eq(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Eq,
            rhs: Box::new(other),
        };
        Elem::Expr(expr)
    }

    /// Creates a new range element that is a boolean of inequality of two range elements
    pub fn neq(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Neq,
            rhs: Box::new(other),
        };
        Elem::Expr(expr)
    }

	/// Creates a new range element that is one range element to the power of another
    pub fn pow(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Exp,
            rhs: Box::new(other),
        };
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
	pub fn is_negative(&self, maximize: bool, analyzer: &impl GraphLike) -> bool {
		match self {
			Elem::Concrete(RangeConcrete { val: Concrete::Int(_, val), ..}) if val < &I256::zero() => true,
			Elem::Dynamic(dy) => {
				if maximize {
					dy.maximize(analyzer).is_negative(maximize, analyzer)
				} else {
					dy.minimize(analyzer).is_negative(maximize, analyzer)
				}
			},
			Elem::Expr(expr) => {
				if maximize {
					expr.maximize(analyzer).is_negative(maximize, analyzer)
				} else {
					expr.minimize(analyzer).is_negative(maximize, analyzer)
				}
			},
			_ => false,
		}
    }

    pub fn pre_evaled_is_negative(&self) -> bool {
		matches!(self, Elem::Concrete(RangeConcrete { val: Concrete::Int(_, val), ..}) if val < &I256::zero())
    }

    pub fn maybe_concrete(&self) -> Option<RangeConcrete<Concrete>> {
    	match self {
    		Elem::Concrete(a) => Some(a.clone()),
    		_ => None
    	}
    }

    pub fn maybe_range_dyn(&self) -> Option<RangeDyn<Concrete>> {
    	match self {
    		Elem::ConcreteDyn(a) => Some(*a.clone()),
    		_ => None
    	}
    }
}

impl RangeElem<Concrete> for Elem<Concrete> {
    fn range_eq(&self, other: &Self) -> bool {
    	match (self, other) {
    		(Self::Concrete(a), Self::Concrete(b)) => {
    			a.range_eq(b)
    		}
    		_ => false,
    	}
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
    	match (self, other) {
    		(Self::Concrete(a), Self::Concrete(b)) => {
    			let ord = a.range_ord(b);
    			if ord.is_none() {
    				println!("couldnt compare: {:?} {:?}", a, b);
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
    		Self::ConcreteDyn(d) => d.dependent_on(),
    		Self::Null => vec![]
    	}
    }

	fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
		match self {
    		Self::Dynamic(d) => d.update_deps(mapping),
    		Self::Concrete(_) => {},
    		Self::Expr(expr) => expr.update_deps(mapping),
    		Self::ConcreteDyn(d) => d.update_deps(mapping),
    		Self::Null => {},
    	}
	}

	fn filter_recursion(&mut self, node_idx: NodeIdx, old: Self) {
		match self {
    		Self::Dynamic(d) => {
    			if d.idx == node_idx { *self = old }
    		},
    		Self::Concrete(_) => {},
    		Self::Expr(expr) => expr.filter_recursion(node_idx, old),
    		Self::ConcreteDyn(d) => d.filter_recursion(node_idx, old),
    		Self::Null => {},
    	}
    	// println!("filter recursion {:?}", self);
	}

	fn maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.maximize(analyzer),
			Concrete(inner) => inner.maximize(analyzer),
			ConcreteDyn(inner) => inner.maximize(analyzer),
			Expr(expr) => expr.maximize(analyzer),
			Null => Elem::Null,
		}
	}

	fn minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.minimize(analyzer),
			Concrete(inner) => inner.minimize(analyzer),
			ConcreteDyn(inner) => inner.minimize(analyzer),
			Expr(expr) => expr.minimize(analyzer),
			Null => Elem::Null,
		}
	}

	fn simplify_maximize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.simplify_maximize(analyzer),
			Concrete(inner) => inner.simplify_maximize(analyzer),
			ConcreteDyn(inner) => inner.simplify_maximize(analyzer),
			Expr(expr) => expr.simplify_maximize(analyzer),
			Null => Elem::Null,
		}
	}

	fn simplify_minimize(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.simplify_minimize(analyzer),
			Concrete(inner) => inner.simplify_minimize(analyzer),
			ConcreteDyn(inner) => inner.simplify_minimize(analyzer),
			Expr(expr) => expr.simplify_minimize(analyzer),
			Null => Elem::Null,
		}
	}
}

impl Add for Elem<Concrete> {
    type Output = Self;

    fn add(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Add,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Sub for Elem<Concrete> {
    type Output = Self;

    fn sub(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Sub,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Mul for Elem<Concrete> {
    type Output = Self;

    fn mul(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Mul,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Div for Elem<Concrete> {
    type Output = Self;

    fn div(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Div,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Shl for Elem<Concrete> {
    type Output = Self;

    fn shl(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Shl,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Shr for Elem<Concrete> {
    type Output = Self;

    fn shr(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Shr,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Rem for Elem<Concrete> {
    type Output = Self;

    fn rem(self, other: Elem<Concrete>) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Mod,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}


impl BitAnd for Elem<Concrete> {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::BitAnd,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl BitOr for Elem<Concrete> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::BitOr,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl BitXor for Elem<Concrete> {
    type Output = Self;

    fn bitxor(self, other: Self) -> Self::Output {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::BitXor,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }
}

impl Elem<Concrete> {
	/// Creates a logical AND of two range elements
    pub fn and(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::And,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }

    /// Creates a logical OR of two range elements
    pub fn or(self, other: Self) -> Self {
        let expr = RangeExpr {
            lhs: Box::new(self),
            op: RangeOp::Or,
            rhs: Box::new(other),
        };
        Self::Expr(expr)
    }

    pub fn maybe_elem_min(&self) -> Option<Self> {
    	match self {
    		Elem::Concrete(RangeConcrete { val, ..}) => Some(Elem::from(Concrete::min(val)?)),
    		_ => None
    	}
    }

    pub fn maybe_elem_max(&self) -> Option<Self> {
    	match self {
    		Elem::Concrete(RangeConcrete { val, ..}) => Some(Elem::from(Concrete::max(val)?)),
    		_ => None
    	}
    }
}


/// For execution of operations to be performed on range expressions
pub trait ExecOp<T> {
	/// Attempts to execute ops by evaluating expressions and applying the op for the left-hand-side
	/// and right-hand-side
	fn exec_op(&self, maximize: bool, analyzer: &impl GraphLike) -> Elem<T>;
	/// Attempts to simplify an expression (i.e. just apply constant folding)
	fn simplify_exec_op(&self, maximize: bool, analyzer: &impl GraphLike) -> Elem<T>;
}

impl ExecOp<Concrete> for RangeExpr<Concrete> {
	fn exec_op(&self, maximize: bool, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let lhs_min = self.lhs.minimize(analyzer);
		let lhs_max = self.lhs.maximize(analyzer);
		let rhs_min = self.rhs.minimize(analyzer);
		let rhs_max = self.rhs.maximize(analyzer);

		let lhs_min_neg = lhs_min.pre_evaled_is_negative();
		let lhs_max_neg = lhs_max.pre_evaled_is_negative();
		let rhs_min_neg = rhs_min.pre_evaled_is_negative();
		let rhs_max_neg = rhs_max.pre_evaled_is_negative();

		// println!("op: {}, lhs_min: {} lhs_max: {}, rhs_min: {}, rhs_max: {}", self.op.to_string(), lhs_min.to_range_string(false, analyzer).s, lhs_max.to_range_string(true, analyzer).s, rhs_min.to_range_string(false, analyzer).s, rhs_max.to_range_string(true, analyzer).s);
		match self.op {
			RangeOp::Add => {
				if maximize {
					// if we are maximizing, the largest value will always just be the the largest value + the largest value
					lhs_max.range_add(&rhs_max).unwrap_or(Elem::Expr(self.clone()))	
				} else {
					lhs_min.range_add(&rhs_min).unwrap_or(Elem::Expr(self.clone()))	
				}
			}
			RangeOp::Sub => {
				if maximize {
					// if we are maximizing, the largest value will always just be the the largest value - the smallest value
					lhs_max.range_sub(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				} else {
					// if we are minimizing, the smallest value will always be smallest value - largest value
					lhs_min.range_sub(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::Mul => {
				if maximize {
					// if we are maximizing, and both mins are negative and both maxes are positive, 
					// we dont know which will be larger of the two (i.e. -1*2**255 * -1*2**255 > 100*100)
					match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
						(true, true, true, true) => {
							// all negative, will be min * min because those are furthest from 0 resulting in the
							// largest positive value
							lhs_min.range_mul(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
						}
						(true, false, true, false) => {
							// we dont know if lhs_max * rhs_min is larger or lhs_min * rhs_max is smaller
							match (lhs_min.range_mul(&rhs_min), lhs_max.range_mul(&rhs_max)) {
								(Some(min_expr), Some(max_expr)) => {
									match min_expr.range_ord(&max_expr) {
										Some(std::cmp::Ordering::Less) => {
											max_expr
										}
										Some(std::cmp::Ordering::Greater) => {
											min_expr
										}
										_ => {
											max_expr
										}
									}
								}
								(None, Some(max_expr)) => {
									max_expr
								}
								(Some(min_expr), None) => {
									min_expr
								}
								(None, None) => Elem::Expr(self.clone())
							}
						}
						(_, false, _, false) => {
							// rhs_max is positive, lhs_max is positive, guaranteed to be largest max value
							lhs_max.range_mul(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
						}
						(false, false, true, true) => {
							// since we are forced to go negative here, values closest to 0 will ensure we get the maximum
							lhs_min.range_mul(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
						}
						(true, true, false, false) => {
							// since we are forced to go negative here, values closest to 0 will ensure we get the maximum
							lhs_max.range_mul(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
						}
						(true, _, true, _) => {
							lhs_min.range_mul(&rhs_min).unwrap_or(Elem::Expr(self.clone()))	
						}
						(false, true, _, _) | (_, _, false, true)=> {
							panic!("unsatisfiable range")
						}
						
					}
				} else {
					match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
						(false, false, false, false) => {
							// rhs_min is positive, lhs_min is positive, guaranteed to be smallest max value
							lhs_min.range_mul(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
						}
						(true, true, true, true) => {
							// all negative, will be max * max because those are closest to 0 resulting in the
							// smallest positive value
							lhs_max.range_mul(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
						}
						(true, false, true, false) => {
							// we dont know if lhs_max * rhs_min is smaller or lhs_min * rhs_max is smaller
							match (lhs_max.range_mul(&rhs_min), lhs_min.range_mul(&rhs_max)) {
								(Some(min_expr), Some(max_expr)) => {
									match min_expr.range_ord(&max_expr) {
										Some(std::cmp::Ordering::Less) => {
											min_expr
										}
										Some(std::cmp::Ordering::Greater) => {
											max_expr
										}
										_ => {
											min_expr
										}
									}
								}
								(None, Some(max_expr)) => {
									max_expr
								}
								(Some(min_expr), None) => {
									min_expr
								}
								(None, None) => Elem::Expr(self.clone())
							}
						}
						(true, _, _, false) => {
							// rhs_max is positive, lhs_min is negative, guaranteed to be largest min value
							lhs_min.range_mul(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
						}
						(_, false, _, true) => {
							// just lhs has a positive value, most negative will be lhs_max, rhs_max
							lhs_max.range_mul(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
						}
						(false, false, true, false) => {
							lhs_max.range_mul(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
						}
						(false, true, _, _) | (_, _, false, true)=> {
							panic!("unsatisfiable range")
						}
					}
				}
			}
			RangeOp::Div => {
				let candidates = vec![
					lhs_min.range_div(&rhs_min),
					lhs_min.range_div(&rhs_max),
					lhs_max.range_div(&rhs_min),
					lhs_max.range_div(&rhs_max),
				];
				let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
					lhs_max.range_gt(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_min.range_gt(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::Lt => {
				if maximize {
					lhs_min.range_lt(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_max.range_lt(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::Gte => {
				if maximize {
					lhs_max.range_gte(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_min.range_gte(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::Lte => {
				if maximize {
					lhs_min.range_lte(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_max.range_lte(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::Eq => {
				if maximize {
					// check if either lhs element is contained by rhs
					match (lhs_min.range_ord(&rhs_min), lhs_min.range_ord(&rhs_max), lhs_min.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Equal), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Equal), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						_ => {}
					}

					match (lhs_max.range_ord(&rhs_min), lhs_max.range_ord(&rhs_max), lhs_max.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Equal), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Equal), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						(_, _, Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
					}

					Elem::Expr(self.clone())
				} else {
					// check if either lhs element is *not* contained by rhs
					match (lhs_min.range_ord(&rhs_min), lhs_min.range_ord(&rhs_max), lhs_min.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Less), _, Some(c))
						| (_, Some(std::cmp::Ordering::Greater), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
						_ => {}
					}

					match (lhs_max.range_ord(&rhs_min), lhs_max.range_ord(&rhs_max), lhs_max.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Less), _, Some(c))
						| (_, Some(std::cmp::Ordering::Greater), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
						(_, _, Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
					}

					Elem::Expr(self.clone())
				}
			}
			RangeOp::Neq => {
				if maximize {
					// check if either lhs element is *not* contained by rhs
					match (lhs_min.range_ord(&rhs_min), lhs_min.range_ord(&rhs_max), lhs_min.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Less), _, Some(c))
						| (_, Some(std::cmp::Ordering::Greater), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						_ => {}
					}

					match (lhs_max.range_ord(&rhs_min), lhs_max.range_ord(&rhs_max), lhs_max.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Less), _, Some(c))
						| (_, Some(std::cmp::Ordering::Greater), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						(_, _, Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
					}

					Elem::Expr(self.clone())
				} else {
					// check if either lhs element is contained by rhs
					match (lhs_min.range_ord(&rhs_min), lhs_min.range_ord(&rhs_max), lhs_min.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Equal), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Equal), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
						_ => {}
					}

					match (lhs_max.range_ord(&rhs_min), lhs_max.range_ord(&rhs_max), lhs_max.maybe_concrete()) {
						(_, _, None) => {}
						(Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Equal), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Less), Some(c))
						| (Some(std::cmp::Ordering::Equal), Some(std::cmp::Ordering::Equal), Some(c))
						=> {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(false),
			                    loc: c.loc
			                })
						}
						(_, Some(std::cmp::Ordering::Equal), Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						(Some(std::cmp::Ordering::Greater), Some(std::cmp::Ordering::Greater), Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						(Some(std::cmp::Ordering::Less), Some(std::cmp::Ordering::Less), Some(c)) => {
							return Elem::Concrete(RangeConcrete {
			                    val: Concrete::Bool(true),
			                    loc: c.loc
			                })
						}
						_ => {}
					}

					Elem::Expr(self.clone())
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
				}
			}
			RangeOp::Not => {
				assert!(matches!(rhs_min, Elem::Null) && matches!(rhs_max, Elem::Null));
				let candidates = vec![
					lhs_min.range_not(),
					lhs_min.range_not(),
				];
				let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});

				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});
				
				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
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
				candidates.sort_by(|a, b| {
					match a.range_ord(b) {
						Some(r) => r,
						_ => std::cmp::Ordering::Less
					}
				});
				
				if candidates.is_empty() {
					return Elem::Expr(self.clone());
				}

				if maximize {
					candidates[candidates.len() - 1].clone()
				} else {
					candidates[0].clone()
				}
			}
			RangeOp::BitAnd => {
				if maximize {
					lhs_max.range_bit_and(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_min.range_bit_and(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::BitOr => {
				if maximize {
					lhs_max.range_bit_or(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_min.range_bit_or(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			RangeOp::BitXor => {
				if maximize {
					lhs_max.range_bit_xor(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
				} else {
					lhs_min.range_bit_xor(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
				}
			}
			_ => Elem::Expr(self.clone())
		}
	}

	fn simplify_exec_op(&self, _maximize: bool, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		todo!();
		// let lhs = self.lhs.simplify(analyzer);
		// let rhs = self.rhs.simplify(analyzer);
		// match self.op {
		// 	RangeOp::Add => {
		// 		lhs.range_add(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Sub => {
		// 		lhs.range_sub(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Mul => {
		// 		lhs.range_mul(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Div => {
		// 		lhs.range_div(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	// RangeOp::Mod => {
		// 	// 	lhs.range_mod(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	// }
		// 	RangeOp::Min => {
		// 		lhs.range_min(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Max => {
		// 		lhs.range_max(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Gt => {
		// 		lhs.range_gt(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Lt => {
		// 		lhs.range_lt(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Gte => {
		// 		lhs.range_gte(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Lte => {
		// 		lhs.range_lte(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Eq => {
		// 		lhs.range_ord_eq(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Neq => {
		// 		lhs.range_neq(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Shl => {
		// 		lhs.range_shl(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Shr => {
		// 		lhs.range_shr(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::And => {
		// 		lhs.range_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Not => {
		// 		assert!(matches!(rhs, Elem::Null));
		// 		lhs.range_not().unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Cast => {
		// 		lhs.range_cast(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::Exp => {
		// 		lhs.range_exp(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::BitAnd => {
		// 		lhs.range_bit_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::BitOr => {
		// 		lhs.range_bit_or(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	RangeOp::BitXor => {
		// 		lhs.range_bit_xor(&rhs).unwrap_or(Elem::Expr(self.clone()))
		// 	}
		// 	_ => Elem::Expr(self.clone())
		// }
	}
}