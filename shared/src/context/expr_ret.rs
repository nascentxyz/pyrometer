use crate::analyzer::AsDotStr;
use crate::context::GraphError;
use crate::{ContextVarNode, GraphLike, Node, NodeIdx, VarType};

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExprRet {
    CtxKilled,
    Single(NodeIdx),
    SingleLiteral(NodeIdx),
    Multi(Vec<ExprRet>),
}

impl ExprRet {
    pub fn debug_str(&self, analyzer: &impl GraphLike) -> String {
        match self {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => match analyzer.node(*inner) {
                Node::ContextVar(_) => ContextVarNode::from(*inner).display_name(analyzer).unwrap(),
                e => format!("{:?}", e),
            },
            ExprRet::Multi(inner) => {
                format!(
                    "[{}]",
                    inner
                        .iter()
                        .map(|i| i.debug_str(analyzer))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            ExprRet::CtxKilled => "CtxKilled".to_string(),
        }
    }

    pub fn expect_single(&self) -> Result<NodeIdx, GraphError> {
        match self {
            ExprRet::Single(inner) => Ok(*inner),
            ExprRet::SingleLiteral(inner) => Ok(*inner),
            ExprRet::Multi(inner) if inner.len() == 1 => Ok(inner[0].expect_single()?),
            e => Err(GraphError::ExpectedSingle(format!(
                "Expected a single return got: {e:?}"
            ))),
        }
    }

    pub fn is_single(&self) -> bool {
        match self {
            ExprRet::Single(_inner) => true,
            ExprRet::SingleLiteral(_inner) => true,
            ExprRet::Multi(inner) => inner.len() == 1,
            _ => false,
        }
    }

    pub fn is_killed(&self) -> bool {
        matches!(self, ExprRet::CtxKilled)
    }

    pub fn has_fork(&self) -> bool {
        false
    }

    pub fn has_killed(&self) -> bool {
        match self {
            ExprRet::CtxKilled => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_killed()),
            _ => false,
        }
    }

    pub fn has_literal(&self) -> bool {
        match self {
            ExprRet::SingleLiteral(..) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_literal()),
            _ => false,
        }
    }

    pub fn expect_multi(self) -> Vec<ExprRet> {
        match self {
            ExprRet::Multi(inner) => inner,
            _ => panic!("Expected a multi return got single"),
        }
    }

    pub fn try_as_func_input_str(&self, analyzer: &impl GraphLike) -> String {
        match self {
            ExprRet::Single(inner) | ExprRet::SingleLiteral(inner) => {
                let idx = inner;
                match VarType::try_from_idx(analyzer, *idx) {
                    Some(var_ty) => format!("({})", var_ty.as_dot_str(analyzer)),
                    None => "UnresolvedType".to_string(),
                }
            }
            ExprRet::Multi(inner) if !self.has_fork() => {
                let mut strs = vec![];
                for ret in inner.iter() {
                    strs.push(ret.try_as_func_input_str(analyzer).replace(['(', ')'], ""));
                }
                format!("({})", strs.join(", "))
            }
            e => todo!("here: {e:?}"),
        }
    }

    pub fn as_flat_vec(&self) -> Vec<NodeIdx> {
        let mut idxs = vec![];
        match self {
            ExprRet::Single(idx) | ExprRet::SingleLiteral(idx) => idxs.push(*idx),
            ExprRet::Multi(inner) => {
                idxs.extend(
                    inner
                        .iter()
                        .flat_map(|expr| expr.as_flat_vec())
                        .collect::<Vec<_>>(),
                );
            }
            _ => {}
        }
        idxs
    }

    pub fn as_vec(&self) -> Vec<ExprRet> {
        match self {
            s @ ExprRet::Single(_) | s @ ExprRet::SingleLiteral(_) => vec![s.clone()],
            ExprRet::Multi(inner) => inner.clone(),
            _ => {
                vec![]
            }
        }
    }

    pub fn flatten(self) -> Self {
        match self {
            ExprRet::Single(_) | ExprRet::SingleLiteral(_) => self,
            ExprRet::Multi(inner) => {
                if inner.len() == 1 {
                    inner[0].to_owned().flatten()
                } else {
                    ExprRet::Multi(inner.into_iter().map(|i| i.flatten()).collect())
                }
            }
            _ => self,
        }
    }
}
