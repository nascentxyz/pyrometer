use crate::analyzer::AsDotStr;
use crate::context::GraphError;
use crate::{ContextVarNode, GraphLike, Node, NodeIdx, VarType};

/// The reason a context was killed
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum KilledKind {
    Ended,
    Unreachable,
    Revert,
    ParseError,
}

impl KilledKind {
    /// Returns a string explanation of the KilledKind
    pub fn analysis_str(&self) -> &str {
        use KilledKind::*;
        match self {
            Ended => "Execution ended here successfully",
            Unreachable => "Unsatisifiable bounds, therefore dead code",
            Revert => "Execution guaranteed to revert here!",
            ParseError => "Unexpected parse error. This is likely a bug or invalid solidity. See the `errors` section of the CLI output or rerun with `--debug` for more information",
        }
    }
}

/// A representation of the evaluation of an expression
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExprRet {
    /// The expression resulted in a killing of the context
    CtxKilled(KilledKind),
    /// The expression resulted in nothing
    Null,
    /// The expression resulted in a single element
    Single(NodeIdx),
    /// The expression resulted in a single element that was a literal
    SingleLiteral(NodeIdx),
    /// The expression resulted in multiple elements
    Multi(Vec<ExprRet>),
}

impl ExprRet {
    /// Converts the expression return into a debug string
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

    /// Take one element from the expression return.
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

    /// Checks if the expression return is a `SingleLiteral`. It returns
    /// a list of bools that match if each is a literal
    pub fn literals_list(&self) -> Result<Vec<bool>, GraphError> {
        match self {
            ExprRet::SingleLiteral(..) => Ok(vec![true]),
            ExprRet::Single(..) => Ok(vec![false]),
            ExprRet::Multi(ref inner) => {
                let mut list = vec![];
                inner.iter().try_for_each(|i| {
                    list.extend(i.literals_list()?);
                    Ok(())
                })?;
                Ok(list)
            }
            e => Err(GraphError::ExpectedSingle(format!(
                "Expected a single return got: {e:?}"
            ))),
        }
    }

    /// Expect the expression result to be the Single variant
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

    /// Expect the expression result to be some length
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

    /// Return whether the expression return is a Single or SingleLiteral
    pub fn is_single(&self) -> bool {
        match self {
            ExprRet::Single(_inner) => true,
            ExprRet::SingleLiteral(_inner) => true,
            ExprRet::Multi(inner) => inner.len() == 1,
            _ => false,
        }
    }

    /// Return whether the expression return resulted in the Context being killed
    pub fn is_killed(&self) -> bool {
        matches!(self, ExprRet::CtxKilled(_))
    }

    /// Return the kind of the killed context if it was killed
    pub fn killed_kind(&self) -> Option<KilledKind> {
        match self {
            ExprRet::CtxKilled(k) => Some(*k),
            ExprRet::Multi(multis) => multis.iter().find_map(|expr_ret| expr_ret.killed_kind()),
            _ => None,
        }
    }

    /// Check if any of the expression returns are killed
    pub fn has_killed(&self) -> bool {
        match self {
            ExprRet::CtxKilled(_) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_killed()),
            _ => false,
        }
    }

    /// Check if any of the expression returns are literals
    pub fn has_literal(&self) -> bool {
        match self {
            ExprRet::SingleLiteral(..) => true,
            ExprRet::Multi(multis) => multis.iter().any(|expr_ret| expr_ret.has_literal()),
            _ => false,
        }
    }

    /// Expect the return to be a multi, and return the inner list. Panics if not mulit
    pub fn expect_multi(self) -> Vec<ExprRet> {
        match self {
            ExprRet::Multi(inner) => inner,
            _ => panic!("Expected a multi return got single"),
        }
    }

    /// Try to convert to a solidity-like function input string, i.e. `(uint256, uint256, bytes32)`
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

    /// Flatten the expression returns recursively into a single list of node indices
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

    /// Convert to a normal vector, does not recurse
    pub fn as_vec(&self) -> Vec<ExprRet> {
        match self {
            s @ ExprRet::Single(_) | s @ ExprRet::SingleLiteral(_) => vec![s.clone()],
            ExprRet::Multi(inner) => inner.clone(),
            _ => {
                vec![]
            }
        }
    }

    /// Flatten into a single ExprRet
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
