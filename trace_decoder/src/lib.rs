//! This library generates an Intermediary Representation (IR) of
//! a block's transactions, given a [BlockTrace] and some additional
//! data represented by [OtherBlockData].
//!
//! A [BlockTrace] is defined as follows:
//! ```ignore
//! pub struct BlockTrace {
//!     /// The state and storage trie pre-images (i.e. the tries before
//!     /// the execution of the current block) in multiple possible formats.
//!     pub trie_pre_images: BlockTraceTriePreImages,
//!     /// Traces and other info per transaction. The index of the transaction
//!     /// within the block corresponds to the slot in this vec.
//!     pub txn_info: Vec<TxnInfo>,
//! }
//! ```
//! The trie preimages are the hashed partial tries at the
//! start of the block. A [TxnInfo] contains all the transaction data
//! necessary to generate an IR.
//!
//! # Usage
//!
//! [The zero-bin prover](https://github.com/topos-protocol/zero-bin/blob/main/prover/src/lib.rs)
//! provides a use case for this library:
//! ```ignore
//!  pub async fn prove(
//!      // In this example, [self] is a [ProverInput] storing a [BlockTrace] and
//!      // [OtherBlockData].
//!      self,
//!      runtime: &Runtime,
//!      previous: Option<PlonkyProofIntern>,
//!  ) -> Result<GeneratedBlockProof> {
//!      let block_number = self.get_block_number();
//!      info!("Proving block {block_number}");
//!
//!      let other_data = self.other_data;
//!      // The method calls [into_txn_proof_gen_ir] (see below) to
//!      // generate an IR for each block transaction.
//!      let txs = self.block_trace.into_txn_proof_gen_ir(
//!          &ProcessingMeta::new(resolve_code_hash_fn),
//!          other_data.clone(),
//!      )?;
//!
//!      // The block IRs are provided to the prover to generate an
//!      // aggregation proof.
//!      let agg_proof = IndexedStream::from(txs)
//!          .map(&TxProof)
//!          .fold(&AggProof)
//!          .run(runtime)
//!          .await?;
//!
//!      
//!      if let AggregatableProof::Agg(proof) = agg_proof {
//!          let prev = previous.map(|p| GeneratedBlockProof {
//!              b_height: block_number.as_u64() - 1,
//!              intern: p,
//!          });
//!
//!          // The final aggregation proof is then used to prove the
//!          // current block.
//!          let block_proof = Literal(proof)
//!              .map(&BlockProof { prev })
//!              .run(runtime)
//!              .await?;
//!
//!          info!("Successfully proved block {block_number}");
//!          Ok(block_proof.0)
//!      } else {
//!          bail!("AggProof is is not GeneratedAggProof")
//!      }
//!  }
//! ```
//!
//! As we see in the example, to turn a [BlockTrace] into a
//! vector of IRs, one must call the method
//! [into_txn_proof_gen_ir](BlockTrace::into_txn_proof_gen_ir):
//! ```ignore
//! pub fn into_txn_proof_gen_ir<F>(
//!     self,
//!     // Specifies the way code hashes should be dealt with.
//!     p_meta: &ProcessingMeta<F>,
//!     // Extra data needed for proof generation.
//!     other_data: OtherBlockData,
//! ) -> TraceParsingResult<Vec<GenerationInputs>>
//! ```
//!
//! It first preprocesses the [BlockTrace] to provide transaction,
//! withdrawals and tries data that can be directly used to generate an IR.
//! For each transaction,
//! [into_txn_proof_gen_ir](BlockTrace::into_txn_proof_gen_ir) extracts the
//! necessary data from the processed transaction information to
//! return the IR.
//!
//! The IR is used to generate root proofs, then aggregation proofs and finally
//! block proofs. Because aggregation proofs require at least two entries, we
//! pad the vector of IRs thanks to additional dummy payload intermediary
//! representations whenever necessary.
//!
//! ### [Withdrawals](https://ethereum.org/staking/withdrawals) and Padding
//!
//! Withdrawals are all proven together in a dummy payload. A dummy payload
//! corresponds to the IR of a proof with no transaction. They must, however, be
//! proven last. The padding is therefore carried out as follows: If there are
//! no transactions in the block, we add two dummy transactions. The withdrawals
//! -- if any -- are added to the second dummy transaction. If there is only one
//! transaction in the block, we add one dummy transaction. If
//! there are withdrawals, the dummy transaction is at the end. Otherwise, it is
//! added at the start. If there are two or more transactions:
//! - if there are no withdrawals, no dummy transactions are added
//! - if there are withdrawals, one dummy transaction is added at the end, with
//!   all the withdrawals in it.

#![feature(linked_list_cursors)]
#![feature(trait_alias)]
#![feature(iter_array_chunks)]
#![deny(rustdoc::broken_intra_doc_links)]
// #![deny(missing_debug_implementations)]

#[cfg(doc)]
use trace_protocol::TxnInfo;

mod compact {
    pub mod compact_prestate_processing {
        use std::collections::HashMap;

        use mpt_trie::partial_trie::HashedPartialTrie;

        use crate::types::HashedAccountAddr;

        #[derive(Debug, Default)]
        pub(crate) struct PartialTriePreImages {
            pub state: HashedPartialTrie,
            pub storage: HashMap<HashedAccountAddr, HashedPartialTrie>,
        }
    }
}

/// Defines the main functions used to generate the IR.
pub mod decoding;
/// Defines functions that processes a [BlockTrace] so that it is easier to turn
/// the block transactions into IRs.
pub mod processed_block_trace;
pub mod trace_protocol;
/// Defines multiple types used in the other modules.
pub mod types;
/// Defines useful functions necessary to the other modules.
pub mod utils;

use evm_arithmetization::GenerationInputs;
use keccak_hash::H256;
use trace_protocol::BlockTrace;
use types::OtherBlockData;

pub fn entrypoint(
    trace: BlockTrace,
    other: OtherBlockData,
    resolve: impl Fn(H256) -> Vec<u8>,
) -> anyhow::Result<Vec<GenerationInputs>> {
    use anyhow::{bail, Context as _};
    use evm_arithmetization::generation::mpt::AccountRlp;
    use mpt_trie::partial_trie::PartialTrie as _;
    use type1witness::{execution, reshape, wire};

    use crate::compact::compact_prestate_processing::PartialTriePreImages;
    use crate::processed_block_trace::{
        CodeHashResolving, ProcessedBlockTrace, ProcessedBlockTracePreImages,
    };
    use crate::trace_protocol::{
        BlockTraceTriePreImages, CombinedPreImages, SeparateStorageTriesPreImage,
        SeparateTriePreImage, SeparateTriePreImages, TrieCompact, TrieDirect, TrieUncompressed,
    };

    let BlockTrace {
        trie_pre_images,
        code_db,
        txn_info,
    } = trace;

    let pre_images = match trie_pre_images {
        BlockTraceTriePreImages::Separate(SeparateTriePreImages { state, storage }) => {
            ProcessedBlockTracePreImages {
                tries: PartialTriePreImages {
                    state: match state {
                        // TODO(0xaatif): remove this variant
                        SeparateTriePreImage::Uncompressed(TrieUncompressed {}) => {
                            bail!("unsupported format")
                        }
                        SeparateTriePreImage::Direct(TrieDirect(it)) => it,
                    },
                    storage: match storage {
                        // TODO(0xaatif): remove this variant
                        //                the old code just panics here
                        SeparateStorageTriesPreImage::SingleTrie(TrieUncompressed {}) => {
                            bail!("unsupported format")
                        }
                        SeparateStorageTriesPreImage::MultipleTries(it) => it
                            .into_iter()
                            .map(|(k, v)| match v {
                                // TODO(0xaatif): remove this variant
                                //                the old code just panics here
                                SeparateTriePreImage::Uncompressed(TrieUncompressed {}) => {
                                    bail!("unsupported format")
                                }
                                SeparateTriePreImage::Direct(TrieDirect(v)) => Ok((k, v)),
                            })
                            .collect::<Result<_, _>>()?,
                    },
                },
                extra_code_hash_mappings: None,
            }
        }
        BlockTraceTriePreImages::Combined(CombinedPreImages {
            compact: TrieCompact(bytes),
        }) => {
            let instructions =
                wire::parse(&bytes).context("couldn't parse instruction from binary format")?;
            let executions =
                execution::execute(instructions).context("couldn't execute instructions")?;
            if !executions.len() == 1 {
                bail!(
                    "only a single execution is supported, not {}",
                    executions.len()
                )
            };
            let execution = executions.into_vec().remove(0);
            let reshape::Reshape {
                state,
                code,
                storage,
            } = reshape::reshape(execution).context("couldn't reshape execution")?;
            ProcessedBlockTracePreImages {
                tries: PartialTriePreImages {
                    state,
                    storage: storage.into_iter().collect(),
                },
                extra_code_hash_mappings: match code.is_empty() {
                    true => None,
                    false => Some(
                        code.into_iter()
                            .map(|it| (crate::utils::hash(&it), it.into_vec()))
                            .collect(),
                    ),
                },
            }
        }
    };

    let all_accounts_in_pre_images = pre_images
        .tries
        .state
        .items()
        .filter_map(|(addr, data)| {
            data.as_val()
                .map(|data| (addr.into(), rlp::decode::<AccountRlp>(data).unwrap()))
        })
        .collect::<Vec<_>>();

    let code_db = {
        let mut code_db = code_db.unwrap_or_default();
        if let Some(code_mappings) = pre_images.extra_code_hash_mappings {
            code_db.extend(code_mappings);
        }
        code_db
    };

    let mut code_hash_resolver = CodeHashResolving {
        client_code_hash_resolve_f: |it: &ethereum_types::H256| resolve(*it),
        extra_code_hash_mappings: code_db,
    };

    let last_tx_idx = txn_info.len().saturating_sub(1);

    let txn_info = txn_info
        .into_iter()
        .enumerate()
        .map(|(i, t)| {
            let extra_state_accesses = if last_tx_idx == i {
                // If this is the last transaction, we mark the withdrawal addresses
                // as accessed in the state trie.
                other
                    .b_data
                    .withdrawals
                    .iter()
                    .map(|(addr, _)| crate::utils::hash(addr.as_bytes()))
                    .collect::<Vec<_>>()
            } else {
                Vec::new()
            };

            t.into_processed_txn_info(
                &all_accounts_in_pre_images,
                &extra_state_accesses,
                &mut code_hash_resolver,
            )
        })
        .collect::<Vec<_>>();

    Ok(ProcessedBlockTrace {
        tries: pre_images.tries,
        txn_info,
        withdrawals: other.b_data.withdrawals.clone(),
    }
    .into_txn_proof_gen_ir(other)?)
}

/// Like `#[serde(with = "hex")`, but tolerates and emits leading `0x` prefixes
mod hex {
    use std::{borrow::Cow, fmt};

    use serde::{de::Error as _, Deserialize as _, Deserializer, Serializer};

    pub fn serialize<S: Serializer, T>(data: T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: hex::ToHex,
    {
        let s = data.encode_hex::<String>();
        serializer.serialize_str(&format!("0x{}", s))
    }

    pub fn deserialize<'de, D: Deserializer<'de>, T>(deserializer: D) -> Result<T, D::Error>
    where
        T: hex::FromHex,
        T::Error: fmt::Display,
    {
        let bytes = Cow::<[u8]>::deserialize(deserializer)?;
        match bytes.strip_prefix(b"0x") {
            Some(rest) => T::from_hex(rest),
            None => T::from_hex(bytes),
        }
        .map_err(D::Error::custom)
    }
}

mod type1witness {
    //! Based on [this specification](https://gist.github.com/mandrigin/ff7eccf30d0ef9c572bafcb0ab665cff#the-bytes-layout).
    //! Deviations are commented with `BUG`.

    /// Execution of [`Instruction`]s from the wire into a trie.
    ///
    /// Use of a stack machine is amenable to streaming off the wire.
    pub(crate) mod execution;
    pub(crate) mod reshape;
    /// Simple nibble representation.
    mod u4;
    /// Parser combinators for the binary "wire" format.
    ///
    /// Use of [`winnow`] is amenable to streaming off the wire.
    pub(crate) mod wire;

    fn nibbles2nibbles(ours: Vec<u4::U4>) -> mpt_trie::nibbles::Nibbles {
        let mut theirs = mpt_trie::nibbles::Nibbles::default();
        for it in ours {
            theirs.push_nibble_back(it as u8)
        }
        theirs
    }

    #[test]
    fn test() {
        use insta::assert_debug_snapshot;
        use mpt_trie::{partial_trie::PartialTrie as _, trie_ops::ValOrHash};
        use pretty_assertions::assert_eq;

        #[derive(serde::Deserialize)]
        struct Case {
            #[serde(with = "hex")]
            pub bytes: Vec<u8>,
            #[serde(with = "hex", default)]
            pub expected_state_root: Vec<u8>,
        }

        for (ix, case) in
            serde_json::from_str::<Vec<Case>>(include_str!("type1witness/test_cases.json"))
                .unwrap()
                .into_iter()
                .enumerate()
        {
            println!("case {}", ix);
            let instructions = wire::parse(&case.bytes).unwrap();
            assert_debug_snapshot!(instructions);

            let executions = execution::execute(instructions).unwrap();
            assert_debug_snapshot!(executions);
            assert_eq!(executions.len(), 1);
            let execution = executions.first().clone();

            let reshaped = reshape::reshape(execution).unwrap();
            assert_debug_snapshot!(reshaped);
            assert_eq!(
                reshaped.state.hash(),
                ethereum_types::H256::from_slice(&case.expected_state_root)
            );

            for (k, v) in reshaped.state.items() {
                if let ValOrHash::Val(bytes) = v {
                    let storage_root =
                        rlp::decode::<evm_arithmetization::generation::mpt::AccountRlp>(&bytes)
                            .unwrap()
                            .storage_root;
                    if storage_root != crate::utils::hash(&[]) {
                        assert!(reshaped
                            .storage
                            .contains_key(&ethereum_types::H256::from_slice(&k.bytes_be())))
                    }
                }
            }
        }
    }
}
