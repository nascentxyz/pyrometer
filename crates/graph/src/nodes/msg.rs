use crate::{
    nodes::{Builtin, Concrete, ContextNode, ContextVar},
    range::elem::Elem,
    AnalyzerBackend, AsDotStr, GraphBackend, Node,
};

use shared::{GraphError, NodeIdx, RangeArena};

use ethers_core::types::{Address, U256};
use solang_parser::pt::Loc;

#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct MsgNode(pub usize);

impl MsgNode {
    pub fn underlying<'a>(&self, analyzer: &'a impl GraphBackend) -> Result<&'a Msg, GraphError> {
        match analyzer.node(*self) {
            Node::Msg(st) => Ok(st),
            Node::Unresolved(ident) => Err(GraphError::UnknownVariable(format!(
                "Could not find variable: {}",
                ident.name
            ))),
            e => Err(GraphError::NodeConfusion(format!(
                "Node type confusion: expected node to be Msg but it was: {e:?}"
            ))),
        }
    }
}

impl AsDotStr for MsgNode {
    fn as_dot_str(
        &self,
        analyzer: &impl GraphBackend,
        _arena: &mut RangeArena<Elem<Concrete>>,
    ) -> String {
        format!("msg {{ {:?} }}", self.underlying(analyzer).unwrap())
    }
}

impl From<MsgNode> for NodeIdx {
    fn from(val: MsgNode) -> Self {
        val.0.into()
    }
}

impl From<NodeIdx> for MsgNode {
    fn from(idx: NodeIdx) -> Self {
        MsgNode(idx.index())
    }
}

#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct Msg {
    pub data: Option<Vec<u8>>,
    pub sender: Option<Address>,
    pub sig: Option<[u8; 4]>,
    pub value: Option<U256>,
    pub origin: Option<Address>,
    pub gasprice: Option<U256>,
    pub gaslimit: Option<U256>,
}

impl Msg {
    pub fn context_var_from_str(
        &self,
        elem: &str,
        loc: Loc,
        ctx: ContextNode,
        analyzer: &mut impl AnalyzerBackend,
    ) -> Result<ContextVar, GraphError> {
        let (node, name) = match elem {
            "data" => {
                if let Some(d) = self.data.clone() {
                    let c = Concrete::from(d);
                    (analyzer.add_node(Node::Concrete(c)), "msg.data".to_string())
                } else {
                    let b = Builtin::DynamicBytes;
                    let node = analyzer.builtin_or_add(b);
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "msg.data".to_string();
                    var.display_name = "msg.data".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "sender" => {
                if let Some(d) = self.sender {
                    let c = Concrete::from(d);
                    (
                        analyzer.add_node(Node::Concrete(c)),
                        "msg.sender".to_string(),
                    )
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Address);
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "msg.sender".to_string();
                    var.display_name = "msg.sender".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "sig" => {
                if let Some(d) = self.sig {
                    let c = Concrete::from(d);
                    (analyzer.add_node(Node::Concrete(c)), "msg.sig".to_string())
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Bytes(4));
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "msg.sig".to_string();
                    var.display_name = "msg.sig".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "value" => {
                if let Some(d) = self.value {
                    let c = Concrete::from(d);
                    (
                        analyzer.add_node(Node::Concrete(c)),
                        "msg.value".to_string(),
                    )
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Uint(256));
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "msg.value".to_string();
                    var.display_name = "msg.value".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "origin" => {
                if let Some(d) = self.origin {
                    let c = Concrete::from(d);
                    (
                        analyzer.add_node(Node::Concrete(c)),
                        "tx.origin".to_string(),
                    )
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Address);
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "tx.origin".to_string();
                    var.display_name = "tx.origin".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "gasprice" => {
                if let Some(d) = self.gasprice {
                    let c = Concrete::from(d);
                    (
                        analyzer.add_node(Node::Concrete(c)),
                        "tx.gasprice".to_string(),
                    )
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Uint(64));
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.name = "tx.gasprice".to_string();
                    var.display_name = "tx.gasprice".to_string();
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            "gaslimit" => {
                if let Some(d) = self.gaslimit {
                    let c = Concrete::from(d);
                    (analyzer.add_node(Node::Concrete(c)), "".to_string())
                } else {
                    let node = analyzer.builtin_or_add(Builtin::Uint(64));
                    let mut var = ContextVar::new_from_builtin(loc, node.into(), analyzer)?;
                    var.is_tmp = false;
                    var.is_symbolic = true;
                    return Ok(var);
                }
            }
            e => {
                return Err(GraphError::NodeConfusion(format!(
                    "Unknown msg attribute: {e:?}"
                )))
            }
        };

        let mut var = ContextVar::new_from_concrete(loc, ctx, node.into(), analyzer)?;
        var.name.clone_from(&name);
        var.display_name = name;
        var.is_tmp = false;
        var.is_symbolic = true;
        Ok(var)
    }
}
