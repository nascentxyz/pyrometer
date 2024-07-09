mod context_tys;
mod expr_ret;
mod invariants;
mod node;
mod underlying;
mod var;

pub use context_tys::{CallFork, ContextCache, ModifierState};
pub use expr_ret::{ExprRet, KilledKind};
pub use node::ContextNode;
pub use underlying::Context;
pub use var::{ContextVar, ContextVarNode, TmpConstruction};

// ContextNode implementations are split to ease in maintainability
mod querying;
mod solving;
mod typing;
mod variables;
mod versioning;
