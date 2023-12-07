

impl ContextVarNode {
	#[tracing::instrument(level = "trace", skip_all)]
    pub fn update_deps(
        &mut self,
        ctx: ContextNode,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
    ) -> Result<(), GraphError> {
        if let Some(mut range) = self.range(analyzer)? {
            range.update_deps(*self, ctx, analyzer);
            self.set_range_min(analyzer, range.min)?;
            self.set_range_max(analyzer, range.max)?;
        }
        Ok(())
    }

    pub fn range(&self, analyzer: &impl GraphLike) -> Result<Option<SolcRange>, GraphError> {
        self.underlying(analyzer)?.ty.range(analyzer)
    }

    pub fn range_string(&self, analyzer: &impl GraphLike) -> Result<Option<String>, GraphError> {
        if let Some(range) = self.ref_range(analyzer)? {
            Ok(Some(format!(
                "[ {}, {} ]",
                range
                    .evaled_range_min(analyzer)?
                    .to_range_string(false, analyzer)
                    .s,
                range
                    .evaled_range_max(analyzer)?
                    .to_range_string(true, analyzer)
                    .s
            )))
        } else {
            Ok(None)
        }
    }

    pub fn ref_range<'a>(
        &self,
        analyzer: &'a impl GraphLike,
    ) -> Result<Option<std::borrow::Cow<'a, SolcRange>>, GraphError> {
        self.underlying(analyzer)?.ty.ref_range(analyzer)
    }

    pub fn range_min(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_min().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn range_max(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_max().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_min(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_min(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_max(
        &self,
        analyzer: &impl GraphLike,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_max(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn as_range_elem(
        &self,
        analyzer: &impl GraphLike,
        loc: Loc,
    ) -> Result<Elem<Concrete>, GraphError> {
        match self.underlying(analyzer)?.ty {
            VarType::Concrete(c) => Ok(Elem::Concrete(RangeConcrete {
                val: c.underlying(analyzer)?.clone(),
                loc,
            })),
            _ => Ok(Elem::from(*self)),
        }
    }

    pub fn cache_range(&self, analyzer: &mut impl GraphLike) -> Result<(), GraphError> {
        if let Some(mut range) = self.range(analyzer)? {
            range.cache_eval(analyzer)?;
            self.set_range(analyzer, range)?;
        }
        Ok(())
    }

    pub fn set_range(
        &self,
        analyzer: &mut impl GraphLike,
        new_range: SolcRange,
    ) -> Result<(), GraphError> {
        let underlying = self.underlying_mut(analyzer)?;
        underlying.set_range(new_range);
        Ok(())
    }

    pub fn fallback_range(
        &self,
        analyzer: &mut impl GraphLike,
    ) -> Result<Option<SolcRange>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        underlying.fallback_range(analyzer)
    }

    pub fn needs_fallback(&self, analyzer: &impl GraphLike) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.needs_fallback())
    }
    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_min(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_min: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        if new_min.contains_node((*self).into()) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into());
            } else {
                return Err(GraphError::UnbreakableRecursion(format!("The variable {}'s range is self-referential and we cannot break the recursion.", self.display_name(analyzer)?)));
            }
        }

        tracing::trace!(
            "setting range minimum: {} (node idx: {}), current:\n{:#?}, new_min:\n{:#?}",
            self.display_name(analyzer)?,
            self.0,
            self.range_min(analyzer)?,
            new_min
        );

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.set_range_min(analyzer, new_min)?;
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            self.underlying_mut(analyzer)?
                .set_range_min(new_min, fallback);
        }
        self.cache_range(analyzer)?;
        Ok(())
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_max(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_max: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        if new_max.contains_node((*self).into()) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into());
            }
        }

        tracing::trace!(
            "setting range maximum: {:?}, {}, current:\n{:#?}, new:\n{:#?}",
            self,
            self.display_name(analyzer)?,
            self.ref_range(analyzer)?.unwrap().range_max(), // .unwrap()
            new_max
        );

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.set_range_max(analyzer, new_max)?;
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };

            self.underlying_mut(analyzer)?
                .set_range_max(new_max, fallback)
        }

        self.cache_range(analyzer)?;
        Ok(())
    }

    pub fn set_range_exclusions(
        &self,
        analyzer: &mut impl GraphLike,
        new_exclusions: Vec<Elem<Concrete>>,
    ) -> Result<(), GraphError> {
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };
        self.underlying_mut(analyzer)?
            .set_range_exclusions(new_exclusions, fallback);
        Ok(())
    }

    pub fn try_set_range_min(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_min: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        if new_min.contains_node((*self).into()) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into());
            }
        }

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.try_set_range_min(analyzer, new_min)
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            Ok(self
                .underlying_mut(analyzer)?
                .try_set_range_min(new_min, fallback))
        }
    }

    pub fn try_set_range_max(
        &self,
        analyzer: &mut (impl GraphLike + AnalyzerLike),
        mut new_max: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        if new_max.contains_node((*self).into()) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into());
            }
        }

        if self.is_concrete(analyzer)? {
            let mut new_ty = self.ty(analyzer)?.clone();
            new_ty.concrete_to_builtin(analyzer)?;
            self.underlying_mut(analyzer)?.ty = new_ty;
            self.try_set_range_max(analyzer, new_max)
        } else {
            let fallback = if self.needs_fallback(analyzer)? {
                self.fallback_range(analyzer)?
            } else {
                None
            };
            Ok(self
                .underlying_mut(analyzer)?
                .try_set_range_max(new_max, fallback))
        }
    }

    pub fn try_set_range_exclusions(
        &self,
        analyzer: &mut impl GraphLike,
        new_exclusions: Vec<Elem<Concrete>>,
    ) -> Result<bool, GraphError> {
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };
        Ok(self
            .underlying_mut(analyzer)?
            .try_set_range_exclusions(new_exclusions, fallback))
    }

    pub fn range_deps(&self, analyzer: &impl GraphLike) -> Result<Vec<Self>, GraphError> {
        if let Some(range) = self.ref_range(analyzer)? {
            Ok(range.dependent_on())
        } else {
            Ok(vec![])
        }
    }

    pub fn sol_delete_range(&mut self, analyzer: &mut impl GraphLike) -> Result<(), GraphError> {
        let ty = self.ty(analyzer)?;
        if let Some(delete_range) = ty.delete_range_result(analyzer)? {
            self.set_range(analyzer, delete_range)?;
        }
        Ok(())
    }
}