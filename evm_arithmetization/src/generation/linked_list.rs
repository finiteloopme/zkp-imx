use std::collections::HashSet;
use std::fmt;

use anyhow::Result;
use env_logger::try_init_from_env;
use env_logger::Env;
use env_logger::DEFAULT_FILTER_ENV;
use ethereum_types::{Address, H160, U256};
use itertools::Itertools;
use num::traits::ToBytes;
use plonky2::field::goldilocks_field::GoldilocksField as F;
use plonky2_maybe_rayon::rayon::iter;
use rand::{thread_rng, Rng};

use crate::cpu::kernel::aggregator::KERNEL;
use crate::cpu::kernel::constants::global_metadata::GlobalMetadata;
use crate::cpu::kernel::interpreter::Interpreter;
use crate::memory::segments::Segment::{self, AccessedAddresses, AccessedStorageKeys};
use crate::util::u256_to_usize;
use crate::witness::errors::ProgramError;
use crate::witness::errors::ProverInputError;
use crate::witness::errors::ProverInputError::InvalidInput;
use crate::witness::memory::MemoryAddress;

// A linked list implemented using a vector `access_list_mem`.
// In this representation, the values of nodes are stored in the range
// `access_list_mem[i..i + node_size - 1]`, and `access_list_mem[i + node_size -
// 1]` holds the address of the next node, where i = node_size * j.
#[derive(Clone)]
pub(crate) struct LinkedList<'a, const N: usize> {
    mem: &'a [Option<U256>],
    mem_len: usize,
    offset: usize,
    pos: usize,
}

pub(crate) fn empty_list_mem<const N: usize>(segment: Segment) -> [U256; N] {
    std::array::from_fn(|i| {
        if i == 0 {
            U256::MAX
        } else if i == N - 1 {
            (segment as usize).into()
        } else {
            U256::zero()
        }
    })
}

impl<'a, const N: usize> LinkedList<'a, N> {
    pub fn from_mem_and_segment(
        mem: &'a [Option<U256>],
        segment: Segment,
    ) -> Result<Self, ProgramError> {
        Self::from_mem_len_and_segment(mem, mem.len(), segment)
    }

    pub fn from_mem_len_and_segment(
        mem: &'a [Option<U256>],
        mem_len: usize,
        segment: Segment,
    ) -> Result<Self, ProgramError> {
        if mem.is_empty() {
            return Err(ProgramError::ProverInputError(InvalidInput));
        }
        let mem_len = mem.len();
        Ok(Self {
            mem,
            mem_len,
            offset: segment as usize,
            pos: 0,
        })
    }
}

impl<'a, const N: usize> fmt::Debug for LinkedList<'a, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Linked List {{");
        let cloned_list = self.clone();
        for node in cloned_list {
            if node[0] == U256::MAX {
                writeln!(f, "{:?}", node);
                break;
            }
            writeln!(f, "{:?} ->", node);
        }
        write!(f, "}}")
    }
}

impl<'a, const N: usize> Iterator for LinkedList<'a, N> {
    type Item = [U256; N];

    fn next(&mut self) -> Option<Self::Item> {
        // The first node is always the special node, so we skip it in the first
        // iteration.
        if let Ok(new_pos) = u256_to_usize(self.mem[self.pos + N - 1].unwrap_or_default()) {
            self.pos = new_pos - self.offset;
            Some(std::array::from_fn(|i| {
                self.mem[self.pos + i].unwrap_or_default()
            }))
        } else {
            None
        }
    }
}