//! This module consists of traits & blanket implementations that facilitate performing member access operations
//! like `MyStruct.field` or `MyContract.myFunc`

mod builtin_access;
mod contract_access;
mod enum_access;
mod error_access;
mod library_access;
mod list_access;
mod member_trait;
mod struct_access;

pub use builtin_access::*;
pub use contract_access::*;
pub use enum_access::*;
pub use error_access::*;
pub use library_access::*;
pub use list_access::*;
pub use member_trait::*;
pub use struct_access::*;
