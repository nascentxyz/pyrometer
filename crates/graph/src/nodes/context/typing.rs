use crate::{
    nodes::{ContextNode, FunctionNode},
    AnalyzerBackend, GraphBackend, GraphError,
};

impl ContextNode {
    /// Checks if its an anonymous function call (i.e. loop)
    pub fn is_anonymous_fn_call(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;

        Ok(underlying.fn_call.is_none() && underlying.ext_fn_call.is_none() && !underlying.is_fork)
    }

    pub fn has_continuation(
        &self,
        analyzer: &mut impl GraphBackend,
    ) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.continuation_of.is_some())
    }

    /// Returns whether this context is killed or returned
    pub fn killed_or_ret(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        let underlying = self.underlying(analyzer)?;
        Ok(underlying.killed.is_some()
            || (!underlying.ret.is_empty() && underlying.modifier_state.is_none()))
    }

    /// Returns whether the context is killed
    pub fn is_returned(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(!self.underlying(analyzer)?.ret.is_empty())
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
        Ok(self.underlying(analyzer)?.ext_fn_call.is_some())
    }

    /// Checks whether a function is external to the current context
    pub fn is_fn_ext(
        &self,
        fn_node: FunctionNode,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
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
                            .any(|inherited| *inherited == fn_ctrt))
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Returns whether this context *currently* uses unchecked math
    pub fn unchecked(&self, analyzer: &impl GraphBackend) -> Result<bool, GraphError> {
        Ok(self.underlying(analyzer)?.unchecked)
    }

    /// Sets the context to use unchecked math
    pub fn set_unchecked(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.unchecked = true;
        Ok(())
    }

    /// Sets the context to use checked math
    pub fn unset_unchecked(
        &self,
        analyzer: &mut (impl GraphBackend + AnalyzerBackend),
    ) -> Result<(), GraphError> {
        self.underlying_mut(analyzer)?.unchecked = false;
        Ok(())
    }
}
