// Underestimated gas costs. We underestimate because the optimizer may do some work

/// Binary operation gas cost
pub const BIN_OP_GAS: u64 = 2;
/// Internal function call gas cost
pub const FUNC_CALL_GAS: u64 = 5;
/// External functionc all gas cost
pub const EXT_FUNC_CALL_GAS: u64 = 100;
/// Read a storage variable gas cost
pub const SLOAD_GAS: u64 = 10;
/// Set a storage variable gas cost
pub const SSTORE_GAS: u64 = 10;
