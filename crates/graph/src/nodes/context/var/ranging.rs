use crate::{
    nodes::{Concrete, ContextVarNode},
    range::{range_string::ToRangeString, Range, RangeEval},
    AnalyzerBackend, GraphBackend, GraphError, SolcRange, VarType,
};

use crate::range::elem::*;

use solang_parser::pt::Loc;

impl ContextVarNode {
    pub fn range(&self, analyzer: &impl GraphBackend) -> Result<Option<SolcRange>, GraphError> {
        self.underlying(analyzer)?.ty.range(analyzer)
    }

    pub fn range_string(&self, analyzer: &impl GraphBackend) -> Result<Option<String>, GraphError> {
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

    pub fn simplified_range_string(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<String>, GraphError> {
        if let Some(range) = self.ref_range(analyzer)? {
            Ok(Some(format!(
                "[ {}, {} ]",
                range
                    .simplified_range_min(analyzer)?
                    .to_range_string(false, analyzer)
                    .s,
                range
                    .simplified_range_max(analyzer)?
                    .to_range_string(true, analyzer)
                    .s
            )))
        } else {
            Ok(None)
        }
    }

    pub fn ref_range<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<Option<std::borrow::Cow<'a, SolcRange>>, GraphError> {
        self.underlying(analyzer)?.ty.ref_range(analyzer)
    }

    pub fn range_min(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_min().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn range_max(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.range_max().into_owned()))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_min(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_min(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn evaled_range_max(
        &self,
        analyzer: &impl GraphBackend,
    ) -> Result<Option<Elem<Concrete>>, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(Some(r.evaled_range_max(analyzer)?))
        } else {
            Ok(None)
        }
    }

    pub fn as_range_elem(
        &self,
        analyzer: &impl GraphBackend,
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

    pub fn cache_range(&self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        if let Some(mut range) = self.ty_mut(analyzer)?.take_range() {
            // range.cache_flatten(analyzer)?;
            range.cache_eval(analyzer)?;
            self.set_range(analyzer, range)?;
        }
        Ok(())
    }

    pub fn cache_flattened_range(
        &self,
        analyzer: &mut impl GraphBackend,
    ) -> Result<(), GraphError> {
        if let Some(mut range) = self.ty_mut(analyzer)?.take_range() {
            range.cache_flatten(analyzer)?;
            self.set_range(analyzer, range)?;
        }
        Ok(())
    }

    pub fn cache_eval_range(&self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        if let Some(mut range) = self.ty_mut(analyzer)?.take_range() {
            range.cache_eval(analyzer)?;
            self.set_range(analyzer, range)?;
        }
        Ok(())
    }

    pub fn ty_mut<'a>(
        &self,
        analyzer: &'a mut impl GraphBackend,
    ) -> Result<&'a mut VarType, GraphError> {
        Ok(&mut self.underlying_mut(analyzer)?.ty)
    }

    pub fn set_range(
        &self,
        analyzer: &mut impl GraphBackend,
        new_range: SolcRange,
    ) -> Result<(), GraphError> {
        let underlying = self.underlying_mut(analyzer)?;
        underlying.set_range(new_range);
        Ok(())
    }

    pub fn fallback_range(
        &self,
        analyzer: &mut impl GraphBackend,
    ) -> Result<Option<SolcRange>, GraphError> {
        let underlying = self.underlying(analyzer)?;
        underlying.fallback_range(analyzer)
    }

    pub fn needs_fallback(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.needs_fallback())
    }

    pub fn range_contains_elem(
        &self,
        elem: Elem<Concrete>,
        analyzer: &impl GraphBackend,
    ) -> Result<bool, GraphError> {
        if let Some(r) = self.ref_range(analyzer)? {
            Ok(r.contains_elem(&elem, analyzer))
        } else {
            Ok(false)
        }
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_min(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        mut new_min: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        assert!(self.latest_version(analyzer) == *self);
        if new_min.recursive_dependent_on(analyzer)?.contains(self) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into(), analyzer);
            } else {
                return Err(GraphError::UnbreakableRecursion(format!("The variable {}'s range is self-referential and we cannot break the recursion.", self.display_name(analyzer)?)));
            }
        }

        new_min.arenaize(analyzer)?;

        // new_min.cache_flatten(analyzer)?;
        // new_min.cache_minimize(analyzer)?;

        tracing::trace!(
            "setting range minimum: {} (node idx: {}), current:{}, new_min:{}, deps: {:#?}",
            self.display_name(analyzer)?,
            self.0,
            self.range_min(analyzer)?.unwrap(),
            new_min,
            new_min.recursive_dependent_on(analyzer)?
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
                .set_range_min(new_min, fallback)?;
        }
        self.cache_range(analyzer)?;
        Ok(())
    }

    // #[tracing::instrument(level = "trace", skip_all)]
    pub fn set_range_max(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        mut new_max: Elem<Concrete>,
    ) -> Result<(), GraphError> {
        assert!(self.latest_version(analyzer) == *self);
        if new_max.recursive_dependent_on(analyzer)?.contains(self) {
            if let Some(prev) = self.previous_or_inherited_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into(), analyzer);
            }
        }

        new_max.arenaize(analyzer)?;

        tracing::trace!(
            "setting range maximum: {:?}, {}, current: {}, new: {}",
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
                .set_range_max(new_max, fallback)?;
        }

        self.cache_range(analyzer)?;
        Ok(())
    }

    pub fn set_range_exclusions(
        &self,
        analyzer: &mut impl GraphBackend,
        new_exclusions: Vec<usize>,
    ) -> Result<(), GraphError> {
        tracing::trace!(
            "setting range exclusions for {}",
            self.display_name(analyzer)?
        );
        assert!(*self == self.latest_version(analyzer));
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };

        // let new_exclusions = new_exclusions
        //     .into_iter()
        //     .map(|excl| analyzer.range_arena_idx_or_upsert(excl))
        // .collect();

        self.underlying_mut(analyzer)?
            .set_range_exclusions(new_exclusions, fallback)?;
        Ok(())
    }

    pub fn try_set_range_min(
        &self,
        analyzer: &mut impl AnalyzerBackend,
        mut new_min: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        assert!(self.latest_version(analyzer) == *self);
        if new_min.recursive_dependent_on(analyzer)?.contains(self) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_min.filter_recursion((*self).into(), prev.into(), analyzer);
            }
        }

        new_min.arenaize(analyzer)?;

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
        analyzer: &mut impl AnalyzerBackend,
        mut new_max: Elem<Concrete>,
    ) -> Result<bool, GraphError> {
        assert!(self.latest_version(analyzer) == *self);
        if new_max.recursive_dependent_on(analyzer)?.contains(self) {
            if let Some(prev) = self.previous_version(analyzer) {
                new_max.filter_recursion((*self).into(), prev.into(), analyzer);
            }
        }

        new_max.arenaize(analyzer)?;

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
        analyzer: &mut impl GraphBackend,
        new_exclusions: Vec<usize>,
    ) -> Result<bool, GraphError> {
        tracing::trace!(
            "setting range exclusions for: {}",
            self.display_name(analyzer).unwrap()
        );
        assert!(*self == self.latest_version(analyzer));
        let fallback = if self.needs_fallback(analyzer)? {
            self.fallback_range(analyzer)?
        } else {
            None
        };

        // let new_exclusions = new_exclusions
        //     .into_iter()
        //     .map(|excl| analyzer.range_arena_idx_or_upsert(excl))
        //     .collect();

        Ok(self
            .underlying_mut(analyzer)?
            .try_set_range_exclusions(new_exclusions, fallback))
    }

    pub fn range_deps(&self, analyzer: &impl GraphBackend) -> Result<Vec<Self>, GraphError> {
        if let Some(range) = self.ref_range(analyzer)? {
            Ok(range.dependent_on(analyzer))
        } else {
            Ok(vec![])
        }
    }

    pub fn sol_delete_range(&mut self, analyzer: &mut impl GraphBackend) -> Result<(), GraphError> {
        let ty = self.ty(analyzer)?;
        if let Some(delete_range) = ty.delete_range_result(analyzer)? {
            self.set_range(analyzer, delete_range)?;
        }
        Ok(())
    }
}
