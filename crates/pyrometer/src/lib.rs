#![allow(clippy::type_complexity)]
mod analyzer;
mod analyzer_backend;
mod builtin_fns;
pub mod graph_backend;
pub mod detector;
pub mod reporter;

pub use analyzer::*;
