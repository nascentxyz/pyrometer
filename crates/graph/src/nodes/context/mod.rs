mod context_tys;
mod expr_ret;
mod node;
mod underlying;
mod var;

pub use node::ContextNode;
pub use underlying::Context;
pub use var::ContextVarNode;
pub use expr_ret::{KilledKind, ExprRet};
pub use context_tys::{ ModifierState, ContextCache, CallFork };


// ContextNode implementations are split to ease in maintainability
mod querying;
mod solving;
mod typing;
mod variables;
mod versioning;