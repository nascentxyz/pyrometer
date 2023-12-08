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
    //  Elem::Concrete(self.clone())
    // }

    fn flatten(
        &self,
        _maximize: bool,
        _analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

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

    fn dependent_on(&self) -> Vec<NodeIdx> {
        vec![]
    }
    fn update_deps(&mut self, _mapping: &BTreeMap<NodeIdx, NodeIdx>) {}

    fn filter_recursion(&mut self, _: NodeIdx, _: NodeIdx) {}

    fn maximize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn minimize(&self, _analyzer: &impl GraphLike) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn simplify_maximize(
        &self,
        _exclude: &mut Vec<NodeIdx>,
        _analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }
    fn simplify_minimize(
        &self,
        _exclude: &mut Vec<NodeIdx>,
        _analyzer: &impl GraphLike,
    ) -> Result<Elem<Concrete>, GraphError> {
        Ok(Elem::Concrete(self.clone()))
    }

    fn cache_maximize(&mut self, _g: &impl GraphLike) -> Result<(), GraphError> {
        Ok(())
    }

    fn cache_minimize(&mut self, _g: &impl GraphLike) -> Result<(), GraphError> {
        Ok(())
    }
    fn uncache(&mut self) {}

    fn contains_op_set(
        &self,
        _: bool,
        _op_set: &[RangeOp],
        _analyzer: &impl GraphLike,
    ) -> Result<bool, GraphError> {
        Ok(false)
    }
}