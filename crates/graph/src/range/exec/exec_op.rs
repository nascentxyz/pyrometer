use crate::{
    nodes::Concrete,
    range::{elem::*, exec::*, exec_traits::*},
    GraphBackend, GraphError,
};

use ethers_core::types::{I256, U256};
use solang_parser::pt::Loc;

impl ExecOp<Concrete> for RangeExpr<Concrete> {
    type GraphError = GraphError;

    #[tracing::instrument(level = "trace", skip_all)]
    fn exec_op(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, Self::GraphError> {
        let idx = self.arena_idx(analyzer);
        if let Some(idx) = idx {
            if let Ok(t) = analyzer.range_arena().ranges[idx].try_borrow() {
                if let Elem::Expr(expr) = &*t {
                    if maximize {
                        if let Some(MinMaxed::Maximized(max)) = &expr.maximized {
                            return Ok(*max.clone());
                        }
                    } else if let Some(MinMaxed::Minimized(min)) = &expr.minimized {
                        return Ok(*min.clone());
                    }
                }
            }
        }

        let res = self.exec(self.spread(analyzer)?, maximize, analyzer)?;

        if let Some(idx) = idx {
            if let Ok(mut t) = analyzer.range_arena().ranges[idx].try_borrow_mut() {
                if let Elem::Expr(expr) = &mut *t {
                    if maximize {
                        expr.maximized = Some(MinMaxed::Maximized(Box::new(res.clone())));
                    } else {
                        expr.minimized = Some(MinMaxed::Minimized(Box::new(res.clone())));
                    }
                }
            }
        }

        Ok(res)
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn cache_exec_op(
        &mut self,
        maximize: bool,
        analyzer: &mut impl GraphBackend,
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

        if let Some(idx) = self.arena_idx(analyzer) {
            if let Ok(mut t) = analyzer.range_arena().ranges[idx].try_borrow_mut() {
                if let Elem::Expr(expr) = &mut *t {
                    if maximize {
                        expr.maximized.clone_from(&self.maximized);
                    } else {
                        expr.minimized.clone_from(&self.minimized);
                    }
                }
            }
        }

        Ok(())
    }

    fn uncache_exec(&mut self) {
        self.lhs.uncache();
        self.rhs.uncache();
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn simplify_exec_op(
        &self,
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if maximize {
            if let Some(v) = &self.flattened_max {
                return Ok(*v.clone());
            }
        } else if let Some(v) = &self.flattened_min {
            return Ok(*v.clone());
        }

        if let Some(v) = self.arenaized_flat_cache(maximize, analyzer) {
            return Ok(*v);
        }

        let (lhs_min, lhs_max, rhs_min, rhs_max) = self.simplify_spread(analyzer)?;
        tracing::trace!(
            "simplifying op: {} {} {}, lhs_min: {}, lhs_max: {}, rhs_min: {}, rhs_max: {}",
            self.lhs,
            self.op.to_string(),
            self.rhs,
            lhs_min,
            lhs_max,
            rhs_min,
            rhs_max
        );
        let lhs_is_conc = lhs_min.is_conc() && lhs_max.is_conc();
        let rhs_is_conc = rhs_min.is_conc() && rhs_max.is_conc();

        let mut finished = false;
        let mut ret = Ok(Elem::Null);
        if self.op == RangeOp::Cast {
            // for a cast we can *actually* evaluate dynamic elem if lhs side is concrete
            if lhs_is_conc {
                ret = self.exec_op(maximize, analyzer);
                finished = true;
            } else {
                // we can drop the cast if the max of the dynamic lhs is less than the cast
                let concretized_lhs = self.lhs.maximize(analyzer)?;
                if matches!(
                    concretized_lhs.range_ord(&self.rhs, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                ) {
                    ret = Ok(*self.lhs.clone());
                    finished = true;
                }
            }
        } else if matches!(self.op, RangeOp::Concat | RangeOp::Memcopy) {
            // we can always execute a concat or memcopy
            ret = self.exec_op(maximize, analyzer);
            finished = true;
        } else if matches!(
            self.op,
            RangeOp::SetIndices | RangeOp::SetLength | RangeOp::GetLength | RangeOp::GetIndex
        ) {
            match self.op {
                RangeOp::GetLength => {
                    ret = if maximize {
                        Ok(lhs_max
                            .range_get_length()
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    } else {
                        Ok(lhs_min
                            .range_get_length()
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    };
                    finished = true;
                }
                RangeOp::SetLength => {
                    ret = if maximize {
                        Ok(lhs_max
                            .range_set_length(&rhs_max)
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    } else {
                        Ok(lhs_min
                            .range_set_length(&rhs_min)
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    };
                    finished = true;
                }
                RangeOp::GetIndex => {
                    if maximize {
                        let res = match lhs_max {
                            Elem::ConcreteDyn(RangeDyn { ref val, .. }) => val
                                .iter()
                                .try_fold(
                                    None,
                                    |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                                        if matches!(
                                            key.overlaps_dual(&rhs_min, &rhs_max, true, analyzer)?,
                                            Some(true)
                                        ) {
                                            if acc.is_none()
                                                || matches!(
                                                    acc.clone().unwrap().range_ord(val, analyzer),
                                                    Some(std::cmp::Ordering::Greater)
                                                )
                                            {
                                                acc = Some(val.clone());
                                                Ok(acc)
                                            } else {
                                                Ok(acc)
                                            }
                                        } else {
                                            Ok(acc)
                                        }
                                    },
                                )?
                                .unwrap_or_else(|| Elem::Null),
                            _ => Elem::Expr(self.clone()),
                        };
                        ret = Ok(res);
                        finished = true;
                    } else {
                        let res = match lhs_max {
                            Elem::ConcreteDyn(RangeDyn { ref val, .. }) => val
                                .iter()
                                .try_fold(
                                    None,
                                    |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                                        if matches!(
                                            key.overlaps_dual(&rhs_min, &rhs_max, true, analyzer)?,
                                            Some(true)
                                        ) {
                                            if acc.is_none()
                                                || matches!(
                                                    acc.clone().unwrap().range_ord(val, analyzer),
                                                    Some(std::cmp::Ordering::Less)
                                                )
                                            {
                                                acc = Some(val.clone());
                                                Ok(acc)
                                            } else {
                                                Ok(acc)
                                            }
                                        } else {
                                            Ok(acc)
                                        }
                                    },
                                )?
                                .unwrap_or_else(|| Elem::Null),
                            _ => Elem::Expr(self.clone()),
                        };
                        ret = Ok(res);
                        finished = true;
                    }
                }
                RangeOp::SetIndices => {
                    ret = if maximize {
                        Ok(lhs_max
                            .range_set_indices(&rhs_max)
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    } else {
                        Ok(lhs_min
                            .range_set_indices(&rhs_min)
                            .unwrap_or_else(|| Elem::Expr(self.clone())))
                    };
                    finished = true;
                }
                _ => unreachable!(),
            }
        }

        let parts = (lhs_min, lhs_max, rhs_min, rhs_max);
        match (lhs_is_conc, rhs_is_conc, finished) {
            (true, true, false) => {
                ret = self.exec(parts, maximize, analyzer);
            }
            (_, _, false) => {
                ret = Ok(Elem::Expr(self.clone()));
            }
            _ => {}
        }

        if let Some(_idx) = self.arena_idx(analyzer) {
            self.set_arenaized_flattened(maximize, ret.clone()?, analyzer);
        }
        ret
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
        self.lhs.set_arenaized_cache(false, &lhs_min, analyzer);

        let lhs_max = self.lhs.maximize(analyzer)?;
        self.lhs.set_arenaized_cache(true, &lhs_max, analyzer);

        let rhs_min = self.rhs.minimize(analyzer)?;
        self.rhs.set_arenaized_cache(false, &rhs_min, analyzer);

        let rhs_max = self.rhs.maximize(analyzer)?;
        self.rhs.set_arenaized_cache(true, &rhs_max, analyzer);

        Ok((lhs_min, lhs_max, rhs_min, rhs_max))
    }

    fn simplify_spread(
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
        let lhs_min = self.lhs.simplify_minimize(analyzer)?;
        self.lhs.set_arenaized_flattened(false, &lhs_min, analyzer);

        let lhs_max = self.lhs.simplify_maximize(analyzer)?;
        self.lhs.set_arenaized_flattened(true, &lhs_max, analyzer);

        let rhs_min = self.rhs.simplify_minimize(analyzer)?;
        self.rhs.set_arenaized_flattened(false, &rhs_min, analyzer);

        let rhs_max = self.rhs.simplify_maximize(analyzer)?;
        self.rhs.set_arenaized_flattened(true, &rhs_max, analyzer);

        Ok((lhs_min, lhs_max, rhs_min, rhs_max))
    }

    #[tracing::instrument(level = "trace", skip_all)]
    fn exec(
        &self,
        (lhs_min, lhs_max, rhs_min, rhs_max): (
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
            Elem<Concrete>,
        ),
        maximize: bool,
        analyzer: &impl GraphBackend,
    ) -> Result<Elem<Concrete>, GraphError> {
        if maximize {
            if let Some(MinMaxed::Maximized(v)) = self.arenaized_cache(maximize, analyzer) {
                tracing::trace!("avoided execing via cache");
                return Ok(*v);
            }
        }

        if !maximize {
            if let Some(MinMaxed::Minimized(v)) = self.arenaized_cache(maximize, analyzer) {
                tracing::trace!("avoided execing via cache");
                return Ok(*v);
            }
        }

        tracing::trace!(
            "executing {}: {} {} {}, lhs_min: {}, lhs_max: {}, rhs_min: {}, rhs_max: {}",
            if maximize { "maximum" } else { "minimum" },
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
            matches!(
                lhs_min.range_ord(&lhs_max, analyzer),
                Some(std::cmp::Ordering::Equal)
            ),
            matches!(
                rhs_min.range_ord(&rhs_max, analyzer),
                Some(std::cmp::Ordering::Equal)
            ),
        );

        fn fallback(
            this: &RangeExpr<Concrete>,
            lhs: Elem<Concrete>,
            rhs: Elem<Concrete>,
            consts: (bool, bool),
        ) -> Elem<Concrete> {
            match consts {
                (true, true) => Elem::Expr(RangeExpr::new(lhs, this.op, rhs)),
                (false, true) => Elem::Expr(RangeExpr::new(*this.lhs.clone(), this.op, rhs)),
                (true, false) => Elem::Expr(RangeExpr::new(lhs, this.op, *this.rhs.clone())),
                (false, false) => Elem::Expr(this.clone()),
            }
        }

        let res = match self.op {
            RangeOp::GetLength => {
                if maximize {
                    let new = lhs_max.clone();
                    let new_max = new.simplify_maximize(analyzer)?;
                    let res = new_max.range_get_length();
                    res.unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    let new_min = lhs_min.simplify_minimize(analyzer)?;
                    let res = new_min.range_get_length();
                    res.unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::SetLength => {
                if maximize {
                    lhs_max
                        .range_set_length(&rhs_max)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                } else {
                    lhs_min
                        .range_set_length(&rhs_min)
                        .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::GetIndex => {
                if maximize {
                    fn match_ty_max(
                        lhs_max: Elem<Concrete>,
                        rhs_min: Elem<Concrete>,
                        rhs_max: Elem<Concrete>,
                        analyzer: &impl GraphBackend,
                    ) -> Result<Elem<Concrete>, GraphError> {
                        match lhs_max {
                            Elem::ConcreteDyn(RangeDyn { val, .. }) => Ok(val
                                .iter()
                                .try_fold(
                                    None,
                                    |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                                        if matches!(
                                            key.overlaps_dual(&rhs_min, &rhs_max, true, analyzer)?,
                                            Some(true)
                                        ) {
                                            if acc.is_none()
                                                || matches!(
                                                    acc.clone().unwrap().range_ord(val, analyzer),
                                                    Some(std::cmp::Ordering::Greater)
                                                )
                                            {
                                                acc = Some(val.clone());
                                                Ok(acc)
                                            } else {
                                                Ok(acc)
                                            }
                                        } else {
                                            Ok(acc)
                                        }
                                    },
                                )?
                                .unwrap_or_else(|| Elem::Null)),
                            Elem::Reference(_) => {
                                let new_max = lhs_max.simplify_maximize(analyzer)?;
                                if new_max == lhs_max {
                                    Ok(Elem::Null)
                                } else {
                                    match_ty_max(new_max, rhs_min, rhs_max, analyzer)
                                }
                            }
                            _ => Ok(Elem::Null),
                        }
                    }
                    match_ty_max(lhs_max.clone(), rhs_min, rhs_max.clone(), analyzer)
                        .unwrap_or_else(|_| fallback(self, lhs_max, rhs_max, consts))
                } else {
                    fn match_ty_min(
                        lhs_min: Elem<Concrete>,
                        rhs_min: Elem<Concrete>,
                        rhs_max: Elem<Concrete>,
                        analyzer: &impl GraphBackend,
                    ) -> Result<Elem<Concrete>, GraphError> {
                        match lhs_min {
                            Elem::ConcreteDyn(RangeDyn { val, .. }) => Ok(val
                                .iter()
                                .try_fold(
                                    None,
                                    |mut acc: Option<Elem<Concrete>>, (key, (val, _))| {
                                        if matches!(
                                            key.overlaps_dual(&rhs_min, &rhs_max, true, analyzer)?,
                                            Some(true)
                                        ) {
                                            if acc.is_none()
                                                || matches!(
                                                    acc.clone().unwrap().range_ord(val, analyzer),
                                                    Some(std::cmp::Ordering::Less)
                                                )
                                            {
                                                acc = Some(val.clone());
                                                Ok(acc)
                                            } else {
                                                Ok(acc)
                                            }
                                        } else {
                                            Ok(acc)
                                        }
                                    },
                                )?
                                .unwrap_or_else(|| Elem::Null)),
                            Elem::Reference(ref _r) => {
                                let new_min = lhs_min.simplify_minimize(analyzer)?;
                                if new_min == lhs_min {
                                    Ok(Elem::Null)
                                } else {
                                    match_ty_min(new_min, rhs_min, rhs_max, analyzer)
                                }
                            }
                            _ => Ok(Elem::Null),
                        }
                    }
                    match_ty_min(lhs_min.clone(), rhs_min.clone(), rhs_max, analyzer)
                        .unwrap_or_else(|_| fallback(self, lhs_min, rhs_min, consts))
                }
            }
            RangeOp::SetIndices => {
                if maximize {
                    let max = self.rhs.simplify_maximize(analyzer)?;

                    lhs_max.range_set_indices(&rhs_max).unwrap_or_else(|| {
                        lhs_max
                            .range_set_indices(&max)
                            .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                    })
                } else {
                    let min = self.rhs.simplify_minimize(analyzer)?;
                    lhs_min.range_set_indices(&rhs_min).unwrap_or_else(|| {
                        lhs_min
                            .range_set_indices(&min)
                            .unwrap_or_else(|| fallback(self, lhs_min, rhs_min, consts))
                    })
                }
            }
            RangeOp::Memcopy => {
                if maximize {
                    lhs_max.clone()
                } else {
                    lhs_min.clone()
                }
            }
            RangeOp::Add(unchecked) => exec_add(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            )
            .unwrap_or_else(|| Elem::Expr(self.clone())),
            RangeOp::Sub(unchecked) => exec_sub(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            )
            .unwrap_or_else(|| Elem::Expr(self.clone())),
            RangeOp::Mul(unchecked) => exec_mul(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            )
            .unwrap_or_else(|| Elem::Expr(self.clone())),
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
                    rhs_min.range_ord(&one, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&one, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_div(&one));
                    candidates.push(lhs_max.range_div(&one));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_div(&negative_one));
                    candidates.push(lhs_max.range_div(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                if !lhs_min.dependent_on(analyzer).is_empty()
                    || !lhs_max.dependent_on(analyzer).is_empty()
                    || !rhs_min.dependent_on(analyzer).is_empty()
                    || !rhs_max.dependent_on(analyzer).is_empty()
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
                    let lhs_max_rhs_min_ord = lhs_max.range_ord(&rhs_min, analyzer);
                    let lhs_min_rhs_max_ord = lhs_min.range_ord(&rhs_max, analyzer);

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
                        lhs_min.range_ord(&lhs_max, analyzer),
                        // check if rhs is constant
                        rhs_min.range_ord(&rhs_max, analyzer),
                        // check if lhs is equal to rhs
                        lhs_min.range_ord(&rhs_min, analyzer),
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
                if !lhs_min.dependent_on(analyzer).is_empty()
                    || !lhs_max.dependent_on(analyzer).is_empty()
                    || !rhs_min.dependent_on(analyzer).is_empty()
                    || !rhs_max.dependent_on(analyzer).is_empty()
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
                        if matches!(
                            lhs_min.range_ord(&rhs_min, analyzer),
                            Some(std::cmp::Ordering::Equal)
                        ) {
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
                            lhs_min.range_ord(&rhs_min, analyzer),
                            Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Less)
                        ) {
                            return Ok(Elem::Concrete(RangeConcrete {
                                val: Concrete::Bool(true),
                                loc,
                            }));
                        }
                    }

                    // check for any overlap
                    let lhs_max_rhs_min_ord = lhs_max.range_ord(&rhs_min, analyzer);
                    let lhs_min_rhs_max_ord = lhs_min.range_ord(&rhs_max, analyzer);

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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                    rhs_min.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_and(&zero));
                    candidates.push(lhs_max.range_bit_and(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_and(&negative_one));
                    candidates.push(lhs_max.range_bit_and(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                    rhs_min.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_or(&zero));
                    candidates.push(lhs_max.range_bit_or(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_or(&negative_one));
                    candidates.push(lhs_max.range_bit_or(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                    rhs_min.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    // if the rhs contains zero, in xor, thats just itself
                    candidates.push(lhs_max.range_bit_xor(&zero));
                }

                let min_contains = matches!(
                    rhs_min.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    rhs_max.range_ord(&negative_one, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    candidates.push(lhs_min.range_bit_xor(&negative_one));
                    candidates.push(lhs_max.range_bit_xor(&negative_one));
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                    lhs_min.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Less) | Some(std::cmp::Ordering::Equal)
                );

                let max_contains = matches!(
                    lhs_max.range_ord(&zero, analyzer),
                    Some(std::cmp::Ordering::Greater) | Some(std::cmp::Ordering::Equal)
                );

                if min_contains && max_contains {
                    match lhs_min {
                        Elem::Concrete(
                            ref r @ RangeConcrete {
                                val: Concrete::Uint(..),
                                ..
                            },
                        ) => candidates.push(Some(Concrete::max_of_type(&r.val).unwrap().into())),
                        Elem::Concrete(
                            ref r @ RangeConcrete {
                                val: Concrete::Int(..),
                                ..
                            },
                        ) => candidates.push(Some(Concrete::min_of_type(&r.val).unwrap().into())),
                        _ => {}
                    }
                }

                let mut candidates = candidates.into_iter().flatten().collect::<Vec<_>>();
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
                candidates.sort_by(|a, b| match a.range_ord(b, analyzer) {
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
