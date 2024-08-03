use crate::nodes::Msg;
use crate::{
    nodes::{Concrete, ContextNode, ContextVarNode},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, ContextEdge, Edge, GraphBackend, Node,
};
use solang_parser::pt::Loc;

use shared::{GraphError, NodeIdx, RangeArena};

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct EnvCtxNode(pub usize);

impl EnvCtxNode {
    pub fn underlying<'a>(
        &self,
        analyzer: &'a impl GraphBackend,
    ) -> Result<&'a EnvCtx, GraphError> {
        match analyzer.node(*self) {
            Node::EnvCtx(st) => Ok(st),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find environment context: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be EnvCtx but it was: {e:?}"
            ))),
        }
    }

    pub fn member_access(
        &self,
        analyzer: &impl GraphBackend,
        name: &str,
    ) -> Result<Option<ContextVarNode>, GraphError> {
        Ok(self.underlying(analyzer)?.get(name))
    }
}

impl AsDotStr for EnvCtxNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        format!("env_ctx {{ {:?} }}", self.underlying(analyzer).unwrap())
    }
}

impl From<EnvCtxNode> for NodeIdx {
    fn from(val: EnvCtxNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for EnvCtxNode {
    fn from(idx: NodeIdx) -> Self {
        EnvCtxNode(idx.index())
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct EnvCtx {
    pub this: Option<ContextVarNode>,
    pub data: Option<ContextVarNode>,
    pub sender: Option<ContextVarNode>,
    pub sig: Option<ContextVarNode>,
    pub value: Option<ContextVarNode>,
    pub origin: Option<ContextVarNode>,
    pub gasprice: Option<ContextVarNode>,
    pub gaslimit: Option<ContextVarNode>,
}

impl From<EnvCtx> for Node {
    fn from(e: EnvCtx) -> Node {
        Node::EnvCtx(e)
    }
}

impl EnvCtx {
    pub fn from_msg(
        analyzer: &mut impl AnalyzerBackend,
        msg: &Msg,
        loc: Loc,
        ctx: ContextNode,
    ) -> Result<Self, GraphError> {
        let data_var = msg.context_var_from_str("data", loc, ctx, analyzer)?;
        let sender_var = msg.context_var_from_str("sender", loc, ctx, analyzer)?;
        let sig_var = msg.context_var_from_str("sig", loc, ctx, analyzer)?;
        let value_var = msg.context_var_from_str("value", loc, ctx, analyzer)?;
        let origin_var = msg.context_var_from_str("origin", loc, ctx, analyzer)?;
        let gasprice_var = msg.context_var_from_str("gasprice", loc, ctx, analyzer)?;
        let gaslimit_var = msg.context_var_from_str("gaslimit", loc, ctx, analyzer)?;
        let data_node = analyzer.add_node(data_var);
        let sender_node = analyzer.add_node(sender_var);
        let sig_node = analyzer.add_node(sig_var);
        let value_node = analyzer.add_node(value_var);
        let origin_node = analyzer.add_node(origin_var);
        let gasprice_node = analyzer.add_node(gasprice_var);
        let gaslimit_node = analyzer.add_node(gaslimit_var);

        Ok(EnvCtx {
            this: None,
            data: Some(data_node.into()),
            sender: Some(sender_node.into()),
            sig: Some(sig_node.into()),
            value: Some(value_node.into()),
            origin: Some(origin_node.into()),
            gasprice: Some(gasprice_node.into()),
            gaslimit: Some(gaslimit_node.into()),
        })
    }

    pub fn set(&mut self, name: &str, val: impl Into<ContextVarNode>) {
        match name {
            "this" => self.this = Some(val.into()),
            "data" => self.data = Some(val.into()),
            "sender" => self.sender = Some(val.into()),
            "sig" => self.sig = Some(val.into()),
            "value" => self.value = Some(val.into()),
            "origin" => self.origin = Some(val.into()),
            "gasprice" => self.gasprice = Some(val.into()),
            "gaslimit" | "gas" => self.gaslimit = Some(val.into()),
            _ => unreachable!(),
        }
    }

    pub fn get(&self, name: &str) -> Option<ContextVarNode> {
        match name {
            "this" => self.this,
            "data" => self.data,
            "sender" => self.sender,
            "sig" => self.sig,
            "value" => self.value,
            "origin" => self.origin,
            "gasprice" => self.gasprice,
            "gaslimit" | "gas" => self.gaslimit,
            _ => None,
        }
    }

    pub fn get_name(name: &str) -> Option<String> {
        match name {
            "this" => Some("this".to_string()),
            "data" => Some("msg.data".to_string()),
            "sender" => Some("msg.sender".to_string()),
            "sig" => Some("msg.sig".to_string()),
            "value" => Some("msg.value".to_string()),
            "origin" => Some("tx.origin".to_string()),
            "gasprice" => Some("tx.gasprice".to_string()),
            "gaslimit" | "gas" => Some("gasleft()".to_string()),
            _ => None,
        }
    }
}
