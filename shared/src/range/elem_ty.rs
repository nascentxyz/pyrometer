use std::collections::BTreeMap;
use crate::range::Range;
use std::ops::*;
use crate::range::range_ops::*;
use crate::context::ContextVarNode;
use crate::{nodes::VarType};
use crate::{Concrete, NodeIdx};
use crate::range::{elem::RangeOp, *};
use solang_parser::pt::Loc;


/// Enumeration of the dynamic element's minimum or maximum
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum DynSide {
	Min,
	Max
}

impl ToString for DynSide {
    fn to_string(&self) -> String {
        match self {
            Self::Min => "range_min".to_string(),
            Self::Max => "range_max".to_string(),
        }
    }
}

/// A dynamic range element value
#[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct Dynamic {
	/// Index of the node that is referenced
	pub idx: NodeIdx,
	/// Whether to use the dynamic element's minimum or maximum
	pub side: DynSide,
	/// Sourcecode location
	pub loc: Loc,
}

impl Dynamic {
	pub fn new(idx: NodeIdx, side: DynSide, loc: Loc) -> Self {
		Self { idx, side, loc }
	}
}

impl RangeElem<Concrete> for Dynamic {
	fn eval(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let (idx, range_side) = (self.idx, self.side);
        let cvar = ContextVarNode::from(idx).underlying(analyzer);
        match &cvar.ty {
            VarType::BuiltIn(_, maybe_range) => {
                if let Some(range) = maybe_range {
                    match range_side {
                        DynSide::Min => {
                            range.range_min().eval(analyzer)
                        }
                        DynSide::Max => {
                            range.range_max().eval(analyzer)
                        }
                    }
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

	fn simplify(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let (idx, range_side) = (self.idx, self.side);
		let var = ContextVarNode::from(idx);

		if !var.is_symbolic(analyzer) {
	        let cvar = var.underlying(analyzer);
	        match &cvar.ty {
	            VarType::BuiltIn(_, maybe_range) => {
	                if let Some(range) = maybe_range {
	                    match range_side {
	                        DynSide::Min => {
	                            range.range_min().eval(analyzer)
	                        }
	                        DynSide::Max => {
	                            range.range_max().eval(analyzer)
	                        }
	                    }
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
	            _ => Elem::Dynamic(*self),
	        }
	    } else {
	    	Elem::Dynamic(*self)
	    }
	}

    fn range_eq(&self, _other: &Self, _analyzer: &impl GraphLike) -> bool {
    	todo!()
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
}

/// A concrete value for a range element
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct RangeConcrete<T> {
	pub val: T,
	pub loc: Loc,
}

impl RangeElem<Concrete> for RangeConcrete<Concrete> {
	fn eval(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}

	fn simplify(&self, _analyzer: &impl GraphLike) -> Elem<Concrete> {
		Elem::Concrete(self.clone())
	}

    fn range_eq(&self, other: &Self, analyzer: &impl GraphLike) -> bool {
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
	    						
	    						a.range_eq(&b, analyzer)
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
    				(Concrete::Int(_, s), Concrete::Int(_, o)) => Some(s.cmp(o)),
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
	fn eval(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		self.exec_op(analyzer)
	}

	fn simplify(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		self.simplify_exec_op(analyzer)
	}

    fn range_eq(&self, _other: &Self, _analyzer: &impl GraphLike) -> bool {
    	todo!()
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
}

/// A core range element.
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub enum Elem<T> {
	/// A range element that is a reference to another node
	Dynamic(Dynamic),
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


impl RangeElem<Concrete> for Elem<Concrete> {
	fn eval(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.eval(analyzer),
			Concrete(inner) => inner.eval(analyzer),
			Expr(expr) => expr.eval(analyzer),
			Null => Elem::Null,
		}
	}

	fn simplify(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		use Elem::*;
		match self {
			Dynamic(dy) => dy.simplify(analyzer),
			Concrete(inner) => inner.simplify(analyzer),
			Expr(expr) => expr.simplify(analyzer),
			Null => Elem::Null,
		}
	}

    fn range_eq(&self, other: &Self, analyzer: &impl GraphLike) -> bool {
    	let lhs = self.eval(analyzer);
    	let rhs = other.eval(analyzer);
    	match (lhs, rhs) {
    		(Self::Concrete(a), Self::Concrete(b)) => {
    			a.range_eq(&b, analyzer)
    		}
    		_ => false
    	}
    }

    fn range_ord(&self, other: &Self) -> Option<std::cmp::Ordering> {
    	match (self, other) {
    		(Self::Concrete(a), Self::Concrete(b)) => {
    			a.range_ord(b)
    		}
    		_ => None,
    	}
    }

    fn dependent_on(&self) -> Vec<ContextVarNode> {
    	match self {
    		Self::Dynamic(d) => d.dependent_on(),
    		Self::Concrete(_) => vec![],
    		Self::Expr(expr) => expr.dependent_on(),
    		Self::Null => vec![]
    	}
    }

	fn update_deps(&mut self, mapping: &BTreeMap<ContextVarNode, ContextVarNode>) {
		match self {
    		Self::Dynamic(d) => d.update_deps(mapping),
    		Self::Concrete(_) => {},
    		Self::Expr(expr) => expr.update_deps(mapping),
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
    		Self::Null => {},
    	}
    	println!("{:?}", self);
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
}


/// For execution of operations to be performed on range expressions
pub trait ExecOp<T> {
	/// Attempts to execute ops by evaluating expressions and applying the op for the left-hand-side
	/// and right-hand-side
	fn exec_op(&self, analyzer: &impl GraphLike) -> Elem<T>;
	/// Attempts to simplify an expression (i.e. just apply constant folding)
	fn simplify_exec_op(&self, analyzer: &impl GraphLike) -> Elem<T>;
}

impl ExecOp<Concrete> for RangeExpr<Concrete> {
	fn exec_op(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let lhs = self.lhs.eval(analyzer);
		let rhs = self.rhs.eval(analyzer);
		match self.op {
			RangeOp::Add => {
				lhs.range_add(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Sub => {
				lhs.range_sub(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Mul => {
				lhs.range_mul(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Div => {
				lhs.range_div(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			// RangeOp::Mod => {
			// 	lhs.range_mod(&rhs).unwrap_or(Elem::Expr(self.clone()))
			// }
			RangeOp::Min => {
				lhs.range_min(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Max => {
				lhs.range_max(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Gt => {
				lhs.range_gt(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Lt => {
				lhs.range_lt(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Gte => {
				lhs.range_gte(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Lte => {
				lhs.range_lte(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Eq => {
				lhs.range_ord_eq(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Neq => {
				lhs.range_neq(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Shl => {
				lhs.range_shl(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Shr => {
				lhs.range_shr(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::And => {
				lhs.range_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Not => {
				assert!(matches!(rhs, Elem::Null));
				lhs.range_not().unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Cast => {
				lhs.range_cast(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Exp => {
				lhs.range_exp(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitAnd => {
				lhs.range_bit_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitOr => {
				lhs.range_bit_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitXor => {
				lhs.range_bit_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			_ => Elem::Expr(self.clone())
		}
	}

	fn simplify_exec_op(&self, analyzer: &impl GraphLike) -> Elem<Concrete> {
		let lhs = self.lhs.simplify(analyzer);
		let rhs = self.rhs.simplify(analyzer);
		match self.op {
			RangeOp::Add => {
				lhs.range_add(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Sub => {
				lhs.range_sub(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Mul => {
				lhs.range_mul(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Div => {
				lhs.range_div(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			// RangeOp::Mod => {
			// 	lhs.range_mod(&rhs).unwrap_or(Elem::Expr(self.clone()))
			// }
			RangeOp::Min => {
				lhs.range_min(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Max => {
				lhs.range_max(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Gt => {
				lhs.range_gt(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Lt => {
				lhs.range_lt(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Gte => {
				lhs.range_gte(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Lte => {
				lhs.range_lte(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Eq => {
				lhs.range_ord_eq(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Neq => {
				lhs.range_neq(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Shl => {
				lhs.range_shl(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Shr => {
				lhs.range_shr(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::And => {
				lhs.range_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Not => {
				assert!(matches!(rhs, Elem::Null));
				lhs.range_not().unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Cast => {
				lhs.range_cast(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::Exp => {
				lhs.range_exp(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitAnd => {
				lhs.range_bit_and(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitOr => {
				lhs.range_bit_or(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			RangeOp::BitXor => {
				lhs.range_bit_xor(&rhs).unwrap_or(Elem::Expr(self.clone()))
			}
			_ => Elem::Expr(self.clone())
		}
	}
}