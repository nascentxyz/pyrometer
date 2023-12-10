use crate::{
    nodes::Concrete,
    range::{elem::*, exec_traits::*},
    GraphBackend, GraphError,
};

use shared::NodeIdx;

use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;

impl ExecOp<Concrete> for RangeExpr<Concrete> {
    type GraphError = GraphError;
    fn cache_exec_op(
        &mut self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<(), GraphError> {
        self.lhs.cache_minimize(analyzer)?;
        self.lhs.cache_maximize(analyzer)?;
        self.rhs.cache_minimize(analyzer)?;
        self.rhs.cache_maximize(analyzer)?;
        let res = self.exec_op(maximize, analyzer)?;
        if maximize {
            self.maximized = Some(MinMaxed::Maximized(Box::new(res)));
        } else {
            self.minimized = Some(MinMaxed::Minimized(Box::new(res)));
        }
        Ok(())
    }

    fn uncache_exec(&mut self) {
        self.lhs.uncache();
        self.rhs.uncache();
    }

    fn simplify_exec_op(
        &self,
        maximize: bool,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        let (lhs_min, lhs_max, rhs_min, rhs_max) = self.simplify_spread(exclude, analyzer)?;
        let lhs_is_conc = lhs_min.maybe_concrete().is_some() && lhs_max.maybe_concrete().is_some();
        let rhs_is_conc = rhs_min.maybe_concrete().is_some() && rhs_max.maybe_concrete().is_some();
        if self.op == RangeOp::Cast {
            // for a cast we can *actually* evaluate dynamic elem if lhs side is concrete
            if lhs_is_conc {
                return self.exec_op(maximize, analyzer);
            } else {
                // we can drop the cast if the max of the dynamic lhs is less than the cast
                let concretized_lhs = self.lhs.maximize(analyzer)?;
                if matches!(
                    concretized_lhs.range_ord(&self.rhs),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                ) {
                    return Ok(*self.lhs.clone());
                }
            }
        }
        let parts = (lhs_min, lhs_max, rhs_min, rhs_max);
        match (lhs_is_conc, rhs_is_conc) {
            (true, true) => self.exec(parts, maximize),
            _ => Ok(Elem::Expr(self.clone())),
        }
    }

    fn spread(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<
        (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        GraphError,
    > {
        let lhs_min = self.lhs.minimize(analyzer)?;
        let lhs_max = self.lhs.maximize(analyzer)?;
        let rhs_min = self.rhs.minimize(analyzer)?;
        let rhs_max = self.rhs.maximize(analyzer)?;
        Ok((lhs_min, lhs_max, rhs_min, rhs_max))
    }

    fn simplify_spread(
        &self,
        exclude: &mut Vec<NodeIdx>,
        analyzer: &impl GraphBackend,
    ) -> Result<
        (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        GraphError,
    > {
        let lhs_min = self.lhs.simplify_minimize(exclude, analyzer)?;
        let lhs_max = self.lhs.simplify_maximize(exclude, analyzer)?;
        let rhs_min = self.rhs.simplify_minimize(exclude, analyzer)?;
        let rhs_max = self.rhs.simplify_maximize(exclude, analyzer)?;
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
            self.lhs,
            self.op.to_string(),
            self.rhs,
            lhs_min,
            lhs_max,
            rhs_min,
            rhs_max
        );

        let lhs_min_neg = lhs_min.pre_evaled_is_negative();
        let lhs_max_neg = lhs_max.pre_evaled_is_negative();
        let rhs_min_neg = rhs_min.pre_evaled_is_negative();
        let rhs_max_neg = rhs_max.pre_evaled_is_negative();

        let consts = (
            matches!(lhs_min.range_ord(&lhs_max), Some(std::cmp::Ordering::Equal)),
            matches!(rhs_min.range_ord(&rhs_max), Some(std::cmp::Ordering::Equal)),
        );

        fn fallback(
            this: &RangeExpr<Concrete>,
            lhs: Elem<Concrete>,
            rhs: Elem<Concrete>,
            consts: (bool, bool),
        ) -> Elem<Concrete> {
            // println!("fallback exec: {} {} {}", this.lhs, this.op.to_string(), this.rhs);
            match consts {
                (true, true) => {
                    // println!("true true: {} {} {}", lhs, this.op.to_string(), rhs);
                    Elem::Expr(RangeExpr::new(lhs, this.op, rhs))
                }
                (false, true) => {
                    // println!("false true: {} {} {}", this.lhs, this.op.to_string(), rhs);
                    Elem::Expr(RangeExpr::new(*this.lhs.clone(), this.op, rhs))
                }
                (true, false) => {
                    // println!("true false: {} {} {}", lhs, this.op.to_string(), this.rhs);
                    Elem::Expr(RangeExpr::new(lhs, this.op, *this.rhs.clone()))
                }
                (false, false) => {
                    // println!("false false: {} {} {}", this.lhs, this.op.to_string(), this.rhs);
                    Elem::Expr(this.clone())
                }
            }
        }

        let res = match self.op {
            RangeOp::Add(unchecked) => {
                if unchecked {
                    let mut candidates = vec![
                        lhs_min.range_wrapping_add(&rhs_min),
                        lhs_min.range_wrapping_add(&rhs_max),
                        lhs_max.range_wrapping_add(&rhs_min),
                        lhs_max.range_wrapping_add(&rhs_max),
                    ];

                    // if they arent constants, we can test a normal add
                    if !matches!(consts, (true, true)) {
                        candidates.push(lhs_max.range_add(&rhs_max));
                        candidates.push(lhs_min.range_add(&rhs_min));
                    }

                    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                    candidates.sort_by(|a, b| match a.range_ord(b) {
                        Some(r) => r,
                        _ => std::cmp::Ordering::Less,
                    });

                    if candidates.is_empty() {
                        return Ok(fallback(self, lhs_min, rhs_min, consts));
                    }

                    if maximize {
                        candidates[candidates.len() - 1].clone()
                    } else {
                        candidates[0].clone()
                    }
                } else if maximize {
                    // if we are maximizing, the largest value will always just be the the largest value + the largest value
                    lhs_max
                        .range_add(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_min
                        .range_add(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::Sub(unchecked) => {
                if unchecked {
                    let mut candidates = vec![];
                    // check if rhs contains zero, if so add lhs_min and max as candidates
                    let zero = Elem::from(Concrete::from(U256::from(0)));
                    let one = Elem::from(Concrete::from(U256::from(1)));
                    let rhs_min_contains_zero = matches!(
                        rhs_min.range_ord(&zero),
                        Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                    );

                    let rhs_max_contains_zero = matches!(
                        rhs_max.range_ord(&zero),
                        Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                    );

                    if rhs_min_contains_zero && rhs_max_contains_zero {
                        candidates.push(Some(lhs_min.clone()));
                        candidates.push(Some(lhs_max.clone()));
                    }

                    // If we have the below case, where the lhs
                    // contains the rhs, we can add zero. Futher more, if
                    // the lhs contains rhs - 1, we can add max as it
                    // would overflow to uint256.max
                    //     zero   min                          max  uint256.max
                    // lhs:  | - - |----------------------------| - - |
                    // rhs:  | - - |--| - - - - - - - - - - - - - - - |
                    match lhs_max.range_ord(&rhs_min) {
                        Some(std::cmp::Ordering::Less) => {
                            // We are going to overflow, zero not possible
                        }
                        Some(std::cmp::Ordering::Equal) => {
                            // We are going to at least be zero,
                            // we may overflow. check if rhs is const, otherwise
                            // add uint256.max as a candidate
                            candidates.push(Some(zero.clone()));
                            if !consts.1 {
                                candidates.push(zero.range_wrapping_sub(&one));
                            }
                        }
                        Some(std::cmp::Ordering::Greater) => {
                            // No guarantees on overflow, check lhs_min
                            match lhs_min.range_ord(&rhs_min) {
                                Some(std::cmp::Ordering::Less) => {
                                    // fully contained, add zero and max
                                    candidates.push(Some(zero.clone()));
                                    candidates.push(zero.range_wrapping_sub(&one));
                                }
                                Some(std::cmp::Ordering::Equal) => {
                                    // We are going to at least be zero,
                                    // we may overflow. check if rhs is const, otherwise
                                    // add uint256.max as a candidate
                                    candidates.push(Some(zero.clone()));
                                    if !consts.1 {
                                        candidates.push(zero.range_wrapping_sub(&one));
                                    }
                                }
                                Some(std::cmp::Ordering::Greater) => {
                                    // current info:
                                    //     zero   min                          max  uint256.max
                                    // lhs:  | - - |----------------------------| - - |
                                    // rhs:  | - |----? - - - - - - - - - - - - - - - |
                                    // figure out where rhs max is
                                    match lhs_min.range_ord(&rhs_max) {
                                        Some(std::cmp::Ordering::Less) => {
                                            //     zero   min
                                            // lhs:  | - - |---?
                                            // rhs:  | - |----|
                                            //          min  max
                                            // Add both
                                            candidates.push(Some(zero.clone()));
                                            candidates.push(zero.range_wrapping_sub(&one));
                                        }
                                        Some(std::cmp::Ordering::Equal) => {
                                            //     zero   min
                                            // lhs:  | - - |---?
                                            // rhs:  | |---|
                                            //        min max
                                            // Add zero
                                            candidates.push(Some(zero.clone()));
                                        }
                                        Some(std::cmp::Ordering::Greater) => {
                                            //     zero   min
                                            // lhs:  | - - |---?
                                            // rhs:  |-----|
                                            //      min   max
                                            // Add nothing
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                        _ => {}
                    }

                    candidates.extend(vec![
                        lhs_min.range_wrapping_sub(&rhs_min),
                        lhs_min.range_wrapping_sub(&rhs_max),
                        lhs_max.range_wrapping_sub(&rhs_min),
                        lhs_max.range_wrapping_sub(&rhs_max),
                    ]);
                    let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                    candidates.sort_by(|a, b| match a.range_ord(b) {
                        Some(r) => r,
                        _ => std::cmp::Ordering::Less,
                    });

                    if candidates.is_empty() {
                        return Ok(fallback(self, lhs_min, rhs_min, consts));
                    }

                    if maximize {
                        candidates[candidates.len() - 1].clone()
                    } else {
                        candidates[0].clone()
                    }
                } else if maximize {
                    // if we are maximizing, the largest value will always just be the the largest value - the smallest value
                    lhs_max
                        .range_sub(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    // if we are minimizing, the smallest value will always be smallest value - largest value
                    lhs_min
                        .range_sub(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
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
                        return Ok(fallback(self, lhs_min, rhs_min, consts));
                    }

                    if maximize {
                        candidates[candidates.len() - 1].clone()
                    } else {
                        candidates[0].clone()
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
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
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
                                (None, None) => fallback(self, lhs_min, rhs_min, consts),
                            }
                        }
                        (_, false, _, false) => {
                            // rhs_max is positive, lhs_max is positive, guaranteed to be largest max value
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (false, false, true, true) => {
                            // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                            lhs_min
                                .range_mul(&rhs_max)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (true, true, false, false) => {
                            // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                            lhs_max
                                .range_mul(&rhs_min)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (true, _, true, _) => lhs_min
                            .range_mul(&rhs_min)
                            .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts)),
                        (false, true, _, _) | (_, _, false, true) => {
                            fallback(self, lhs_min, rhs_min, consts)
                        }
                    }
                } else {
                    match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                        (false, false, false, false) => {
                            // rhs_min is positive, lhs_min is positive, guaranteed to be smallest max value
                            lhs_min
                                .range_mul(&rhs_min)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (true, true, true, true) => {
                            // all negative, will be max * max because those are closest to 0 resulting in the
                            // smallest positive value
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
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
                                (None, None) => fallback(self, lhs_min, rhs_min, consts),
                            }
                        }
                        (true, _, _, false) => {
                            // rhs_max is positive, lhs_min is negative, guaranteed to be largest min value
                            lhs_min
                                .range_mul(&rhs_max)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (_, false, _, true) => {
                            // just lhs has a positive value, most negative will be lhs_max, rhs_max
                            lhs_max
                                .range_mul(&rhs_max)
                                .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                        }
                        (false, false, true, false) => lhs_max
                            .range_mul(&rhs_min)
                            .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts)),
                        (false, true, _, _) | (_, _, false, true) => {
                            fallback(self, lhs_min, rhs_min, consts)
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
                }
                // if maximize {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (true, false, true, false) => {
                //          // we dont know if lhs_min / rhs_min is larger or lhs_max / rhs_max is larger
                //          match (lhs_min.range_div(&rhs_min), lhs_max.range_div(&rhs_max)) {
                //              (Some(min_expr), Some(max_expr)) => {
                //                  match min_expr.range_ord(&max_expr) {
                //                      Some(std::cmp::Ordering::Less) => {
                //                          max_expr
                //                      }
                //                      Some(std::cmp::Ordering::Greater) => {
                //                          min_expr
                //                      }
                //                      _ => {
                //                          max_expr
                //                      }
                //                  }
                //              }
                //              (None, Some(max_expr)) => {
                //                  max_expr
                //              }
                //              (Some(min_expr), None) => {
                //                  min_expr
                //              }
                //              (None, None) => Elem::Expr(self.clone())
                //          }
                //      }
                //      (false, false, true, true) => {
                //          // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                //          lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, true, false, false) => {
                //          // since we are forced to go negative here, values closest to 0 will ensure we get the maximum
                //          lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (_, false, false, _) => {
                //          // lhs is positive, rhs min is positive, guaranteed to give largest
                //          lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (_, false, true, false) => {
                //          // lhs_max is positive and rhs_max is positive, guaranteed to be lhs_max and rhs_max
                //          lhs_max.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, _, true, _) => {
                //          // at this point, its either all trues, or a single false
                //          // given that, to maximize, the only way to get a positive value is to use the most negative values
                //          lhs_min.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
                // } else {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (false, false, false, false) => {
                //          // smallest number will be lhs_min / rhs_min since both are positive
                //          lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, true, true, true) => {
                //          // smallest number will be lhs_max / rhs_min since both are negative
                //          lhs_max.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, true, true, false) => {
                //          // The way to maintain most negative value is lhs_min / rhs_max, all others would go
                //          // positive or guaranteed to be closer to 0
                //          lhs_min.range_div(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, false, true, false) => {
                //          // we dont know if lhs_min / rhs_max is larger or lhs_max / rhs_min is larger
                //          match (lhs_min.range_div(&rhs_max), lhs_max.range_div(&rhs_min)) {
                //              (Some(min_expr), Some(max_expr)) => {
                //                  match min_expr.range_ord(&max_expr) {
                //                      Some(std::cmp::Ordering::Less) => {
                //                          min_expr
                //                      }
                //                      Some(std::cmp::Ordering::Greater) => {
                //                          max_expr
                //                      }
                //                      _ => {
                //                          min_expr
                //                      }
                //                  }
                //              }
                //              (None, Some(max_expr)) => {
                //                  max_expr
                //              }
                //              (Some(min_expr), None) => {
                //                  min_expr
                //              }
                //              (None, None) => Elem::Expr(self.clone())
                //          }
                //      }
                //      (_, false, true, _) => {
                //          // We are going negative here, so it will be most positive / least negative
                //          lhs_max.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, _, false, _) => {
                //          // We are going negative here, so it will be most negative / least positive
                //          lhs_min.range_div(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
                }
                // if maximize {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (true, _, true, _) | (false, _, false, _) => {
                //          // counter-intuitively, we want the maximum value from a call to minimum
                //          // this is due to the symbolic nature of the evaluation. We are still
                //          // using the minimum values but getting the larger of the minimum
                //          lhs_min.range_max(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, _, false, false) => {
                //          rhs_min //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, false, true, _) => {
                //          lhs_min //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
                // } else {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (true, _, true, _) | (false, _, false, _) => {
                //          lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, _, false, false) => {
                //          lhs_min //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, false, true, _) => {
                //          rhs_min //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
                }
                // if maximize {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (true, _, true, _) | (false, _, false, _) => {
                //          lhs_max.range_max(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, _, false, false) => {
                //          rhs_max //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, false, true, _) => {
                //          lhs_max //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
                // } else {
                //  match (lhs_min_neg, lhs_max_neg, rhs_min_neg, rhs_max_neg) {
                //      (_, true, _, true) | (_, false, _, false) => {
                //          // counter-intuitively, we want the minimum value from a call to maximum
                //          // this is due to the symbolic nature of the evaluation. We are still
                //          // using the maximum values but getting the smaller of the maximum
                //          lhs_max.range_min(&rhs_max).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (_, false, true, true) => {
                //          lhs_max //.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (true, true, _, false) => {
                //          rhs_max //lhs_min.range_min(&rhs_min).unwrap_or(Elem::Expr(self.clone()))
                //      }
                //      (false, true, _, _) | (_, _, false, true)=> {
                //          panic!("unsatisfiable range")
                //      }
                //  }
                // }
            }
            RangeOp::Gt => {
                if maximize {
                    lhs_max
                        .range_gt(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_min
                        .range_gt(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::Lt => {
                if maximize {
                    lhs_min
                        .range_lt(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_max
                        .range_lt(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::Gte => {
                if maximize {
                    lhs_max
                        .range_gte(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_min
                        .range_gte(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::Lte => {
                if maximize {
                    lhs_min
                        .range_lte(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_max
                        .range_lte(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::Eq => {
                // prevent trying to eval when we have dependents
                if !lhs_min.dependent_on().is_empty()
                    || !lhs_max.dependent_on().is_empty()
                    || !rhs_min.dependent_on().is_empty()
                    || !rhs_max.dependent_on().is_empty()
                {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

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
                        fallback(self, lhs_min, rhs_min, consts)
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
                // prevent trying to eval when we have dependents
                if !lhs_min.dependent_on().is_empty()
                    || !lhs_max.dependent_on().is_empty()
                    || !rhs_min.dependent_on().is_empty()
                    || !rhs_max.dependent_on().is_empty()
                {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }
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
                    // the only case here in which we can't assert that
                    // true is the maximum is when they are both consts and equal
                    if matches!(consts, (true, true)) {
                        // both are consts, check if they are equal
                        if matches!(lhs_min.range_ord(&rhs_min), Some(std::cmp::Ordering::Equal)) {
                            return Ok(Elem::Concrete(RangeConcrete {
                                val: Concrete::Bool(false),
                                loc,
                            }));
                        }
                    }

                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(true),
                        loc,
                    })
                } else {
                    // we *want* to produce false
                    if matches!(consts, (true, true)) {
                        // both are consts, check if we are forced to return true
                        if matches!(
                            lhs_min.range_ord(&rhs_min),
                            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Less)
                        ) {
                            return Ok(Elem::Concrete(RangeConcrete {
                                val: Concrete::Bool(true),
                                loc,
                            }));
                        }
                    }

                    // check for any overlap
                    let lhs_max_rhs_min_ord = lhs_max.range_ord(&rhs_min);
                    let lhs_min_rhs_max_ord = lhs_min.range_ord(&rhs_max);

                    // if lhs max is less than the rhs min, it has to be != (true)
                    if matches!(lhs_max_rhs_min_ord, Some(std::cmp::Ordering::Less)) {
                        return Ok(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc,
                        }));
                    }

                    // if lhs min is greater than the rhs max, it has to be != (true)
                    if matches!(lhs_min_rhs_max_ord, Some(std::cmp::Ordering::Greater)) {
                        return Ok(Elem::Concrete(RangeConcrete {
                            val: Concrete::Bool(true),
                            loc,
                        }));
                    }

                    // we can force an equal value if needed
                    Elem::Concrete(RangeConcrete {
                        val: Concrete::Bool(false),
                        loc,
                    })
                    // fallback(self, lhs_min, rhs_min, consts)
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
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
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
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
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
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
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
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
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
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
                candidates.sort_by(|a, b| match a.range_ord(b) {
                    Some(r) => r,
                    _ => std::cmp::Ordering::Less,
                });

                if candidates.is_empty() {
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                            ref r @ RangeConcrete {
                                val: Concrete::Uint(..),
                                ..
                            },
                        ) => candidates.push(Some(Elem::from(Concrete::max(&r.val).unwrap()))),
                        Elem::Concrete(
                            ref r @ RangeConcrete {
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
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
                    return Ok(fallback(self, lhs_min, rhs_min, consts));
                }

                if maximize {
                    candidates[candidates.len() - 1].clone()
                } else {
                    candidates[0].clone()
                }
            }
            _ => fallback(self, lhs_min, rhs_min, consts),
        };
        Ok(res)
    }
}
