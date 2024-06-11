//! Columns for the initial or final memory, ordered by address.
//! It contains (addr, value) pairs. Note that non-padding addresses must be
//! unique.
use crate::memory::VALUE_LIMBS;

/// 1 if an actual value or 0 if it's a padding row.
pub(crate) const FILTER: usize = 0;
/// The execution context of the address.
pub(crate) const ADDR_CONTEXT: usize = FILTER + 1;
/// The segment section of this address.
pub(crate) const ADDR_SEGMENT: usize = ADDR_CONTEXT + 1;
/// The virtual address within the given context and segment.
pub(crate) const ADDR_VIRTUAL: usize = ADDR_SEGMENT + 1;

// Eight 32-bit limbs hold a total of 256 bits.
// If a value represents an integer, it is little-endian encoded.
const VALUE_START: usize = ADDR_VIRTUAL + 1;
pub(crate) const fn value_limb(i: usize) -> usize {
    debug_assert!(i < VALUE_LIMBS);
    VALUE_START + i
}

// Flags to indicate whether this part of the address differs from the next row,
// and the previous parts do not differ.
// That is, e.g., `SEGMENT_FIRST_CHANGE` is `F::ONE` iff `ADDR_CONTEXT` is the
// same in this row and the next, but `ADDR_SEGMENT` is not.
pub(crate) const CONTEXT_FIRST_CHANGE: usize = VALUE_START + VALUE_LIMBS;
pub(crate) const SEGMENT_FIRST_CHANGE: usize = CONTEXT_FIRST_CHANGE + 1;
pub(crate) const VIRTUAL_FIRST_CHANGE: usize = SEGMENT_FIRST_CHANGE + 1;

// We use a range check to enforce the ordering. To use less columns, it's split
// between low and high limbs.
pub(crate) const RC_LOW: usize = VIRTUAL_FIRST_CHANGE + 1;
pub(crate) const RC_HIGH: usize = RC_LOW + 1;
/// The counter column (used for the range check) starts from 0 and increments.
pub(crate) const COUNTER: usize = RC_HIGH + 1;
/// The frequencies column used in logUp.
pub(crate) const FREQUENCIES: usize = COUNTER + 1;

pub(crate) const NUM_COLUMNS: usize = FREQUENCIES + 1;
