use crate::analyzer::AsDotStr;
use crate::context::GraphError;
use crate::{ContextVarNode, GraphLike, Node, NodeIdx, VarType};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum KilledKind {
    Ended,
    Unreachable,
    Revert,
}

impl KilledKind {
    pub fn analysis_str(&self) -> &str {
        use KilledKind::*;
        match self {
            Ended => "Execution ended here successfully",
            Unreachable => "Unsatisifiable bounds, therefore dead code",
            Revert => "Execution guaranteed to revert here!",
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExprRet {
    CtxKilled(KilledKind),
    Null,
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
            ExprRet::CtxKilled(kind) => format!("CtxKilled({:?}", kind),
            ExprRet::Null => "<null>".to_string(),
        }
    }

    pub fn take_one(&mut self) -> Result<Option<ExprRet>, GraphError> {
        match self {
            ExprRet::Single(..) | ExprRet::SingleLiteral(..) => {
                let ret = self.clone();
                *self = ExprRet::Multi(vec![]);
                Ok(Some(ret))
            }
            ExprRet::Multi(ref mut inner) => {
                let elem = inner.pop();
                Ok(elem)
            }
            e => Err(GraphError::ExpectedSingle(format!(
                "Expected a single return got: {e:?}"
            ))),
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

    pub fn expect_length(&self, len: usize) -> Result<(), GraphError> {
        match self {
            ExprRet::Single(_) | ExprRet::SingleLiteral(_) => {
                if len == 1 {
                    Ok(())
                } else {
                    Err(GraphError::StackLengthMismatch(format!(
                        "Expected an element with {len} elements, return got: 1 element"
                    )))
                }
            }
            ExprRet::Multi(inner) => {
                if inner.len() == len {
                    Ok(())
                } else {
                    Err(GraphError::StackLengthMismatch(format!(
                        "Expected an element with {len} elements, return got: {} elements",
                        inner.len()
                    )))
                }
            }
            ExprRet::CtxKilled(..) => Err(GraphError::StackLengthMismatch(format!(
                "Expected an element with {len} elements, but context was killed"
            ))),
            ExprRet::Null if len != 0 => Err(GraphError::StackLengthMismatch(format!(
                "Expected an element with {len} elements, return got: 0 elements",
            ))),
            _ => Ok(()),
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
        matches!(self, ExprRet::CtxKilled(_))
    }

    pub fn killed_kind(&self) -> Option<KilledKind> {
        match self {
            ExprRet::CtxKilled(k) => Some(*k),
            ExprRet::Multi(multis) => multis.iter().find_map(|expr_ret| expr_ret.killed_kind()),
            _ => None,
        }
    }

    pub fn has_fork(&self) -> bool {
        false
    }

    pub fn has_killed(&self) -> bool {
        match self {
            ExprRet::CtxKilled(_) => true,
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
                    Some(var_ty) => {
                        if let Ok(ty) = var_ty.unresolved_as_resolved(analyzer) {
                            format!("({})", ty.as_dot_str(analyzer))
                        } else {
                            "<UnresolvedType>".to_string()
                        }
                    }
                    None => "<UnresolvedType>".to_string(),
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
