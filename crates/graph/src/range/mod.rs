//! Ranges consist of a minimum range element and a maximum range element.
//!
//!
//!
//! We define an algebra of types. This means we can perform calculations between two range elements.
//!
//!
//!
//!
//!

pub mod elem;
pub mod exec;
pub mod exec_traits;
pub mod range_string;
mod range_trait;
mod solc_range;

pub use range_trait::*;
pub use solc_range::*;
