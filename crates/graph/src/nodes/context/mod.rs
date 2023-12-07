mod context_tys;
mod expr_ret;
mod node;
mod underlying;

pub use node::ContextNode;
pub use underlying::Context;
pub mod var;


// ContextNode implementations are split to ease in maintainability
mod querying;
mod solving;
mod typing;
mod variables;
mod versioning;