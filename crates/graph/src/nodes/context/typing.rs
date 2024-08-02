use crate::{
    nodes::{context::underlying::SubContextKind, ContextNode, FunctionNode, KilledKind},
    AnalyzerBackend, GraphBackend,
};
use shared::GraphError;

impl ContextNode {
    /// Checks if its an anonymous function call (i.e. loop)
    pub fn is_anonymous_fn_call(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;

        Ok(matches!(
            underlying.subctx_kind,
            Some(SubContextKind::Loop { .. })
        ))
    }

    pub fn increment_parse_idx(&self, analyzer: &mut impl AnalyzerBackend) -> usize {
        let underlying_mut = self.underlying_mut(analyzer).unwrap();
        let curr = underlying_mut.parse_idx;
        underlying_mut.parse_idx += 1;
        curr
    }

    pub fn skip_n_exprs(&self, n: usize, analyzer: &mut impl AnalyzerBackend) {
        let underlying_mut = self.underlying_mut(analyzer).unwrap();
        underlying_mut.parse_idx += n;
    }

    pub fn parse_idx(&self, analyzer: &impl GraphBackend) -> usize {
        self.underlying(analyzer).unwrap().parse_idx
    }

    pub fn has_continuation(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.continuation_of().is_some())
    }

    /// Returns whether this context is killed or returned
    pub fn killed_or_ret(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.killed.is_some()
            || (!underlying.ret.is_empty() && underlying.modifier_state.is_none()))
    }

    /// Returns whether the context is returned
    pub fn is_returned(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(!self.underlying(analyzer)?.ret.is_empty())
    }

    /// Returns whether the context is reverted
    pub fn is_graceful_ended(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(matches!(
            self.underlying(analyzer)?.killed,
            Some((_, KilledKind::Ended))
        ))
    }

    /// Returns whether the context is killed
    pub fn is_killed(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.killed.is_some())
    }

    /// Returns whether the context is killed
    pub fn is_ended(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.child.is_some() || underlying.killed.is_some() || !underlying.ret.is_empty())
    }

    /// Check if this context is in an external function call
    pub fn is_ext_fn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_ext_fn_call())
    }

    /// Checks whether a function is external to the current context
    pub fn is_fn_ext(
        &self,
        fn_node: FunctionNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<bool, GraphError> {
        match fn_node.maybe_associated_contract(analyzer) {
            None => Ok(false),
            Some(fn_ctrt) => {
                if let Some(self_ctrt) = self
                    .associated_fn(analyzer)?
                    .maybe_associated_contract(analyzer)
                {
                    Ok(Some(self_ctrt) != Some(fn_ctrt)
                        && !self_ctrt
                            .underlying(analyzer)?
                            .inherits
                            .iter()
                            .filter_map(|i| i.as_ref())
                            .any(|inherited| *inherited == fn_ctrt))
                } else {
                    Ok(false)
                }
            }
        }
    }
}
