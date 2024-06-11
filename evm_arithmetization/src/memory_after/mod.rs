//! The MemAfter STARK is used to store the memory state at the end of the
//! execution. It connects to the memory STARK to read the final values of all
//! touched addresses.

pub mod columns;
pub mod memory_after_stark;

/// The range-check value. Note that differences are range-checked against
/// RANGE_CHECK^2.
pub(crate) const RANGE_CHECK: usize = 1024;
