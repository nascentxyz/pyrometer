use crate::{
    nodes::{context::underlying::SubContextKind, CallFork, ContextNode, KilledKind},
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

    pub fn has_live_edge(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        match underlying.child {
            Some(CallFork::Call(c)) => c.has_live_edge(analyzer),
            Some(CallFork::Fork(w1, w2)) => {
                let w1live = w1.has_live_edge(analyzer)?;
                let w2live = w2.has_live_edge(analyzer)?;
                Ok(w1live || w2live)
            }
            None => Ok(underlying.ret.is_empty() && underlying.killed.is_none()),
        }
    }

    /// Check if this context is in an external function call
    pub fn is_ext_fn(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.is_ext_fn_call())
    }
}
