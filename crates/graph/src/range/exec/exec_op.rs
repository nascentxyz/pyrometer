use crate::{
    nodes::Concrete,
    range::{elem::*, exec::*, exec_traits::*},
    GraphBackend, GraphError,
};

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

        let res = match self.op {
            RangeOp::GetLength => exec_get_length(&lhs_min, &lhs_max, maximize, analyzer),
            RangeOp::GetIndex => {
                exec_get_index(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::SetLength => {
                exec_set_length(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::SetIndices => exec_set_indices(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, &*self.rhs, maximize, analyzer,
            ),
            RangeOp::Memcopy => exec_memcopy(&lhs_min, &lhs_max, maximize),
            RangeOp::Concat => {
                exec_concat(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::Add(unchecked) => exec_add(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            ),
            RangeOp::Sub(unchecked) => exec_sub(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            ),
            RangeOp::Mul(unchecked) => exec_mul(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            ),
            RangeOp::Div(unchecked) => exec_div(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, unchecked, analyzer,
            ),
            RangeOp::Mod => exec_mod(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Exp => exec_exp(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Min => exec_min(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Max => exec_max(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Gt => exec_gt(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize),
            RangeOp::Lt => exec_lt(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize),
            RangeOp::Gte => exec_gte(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize),
            RangeOp::Lte => exec_lte(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize),
            RangeOp::Eq => exec_eq_neq(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, true, analyzer,
            ),
            RangeOp::Neq => exec_eq_neq(
                &lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, false, analyzer,
            ),
            RangeOp::And => exec_and(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Or => exec_or(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Not => exec_not(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::BitAnd => {
                exec_bit_and(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::BitOr => {
                exec_bit_or(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::BitXor => {
                exec_bit_or(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer)
            }
            RangeOp::BitNot => exec_bit_not(&lhs_min, &lhs_max, maximize, analyzer),
            RangeOp::Shl => exec_shl(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Shr => exec_shr(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
            RangeOp::Cast => exec_cast(&lhs_min, &lhs_max, &rhs_min, &rhs_max, maximize, analyzer),
        };
        Ok(res.unwrap_or_else(|| Elem::Expr(self.clone())))
    }
}
