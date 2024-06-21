use std::collections::HashMap;
use std::time::Duration;

use ethereum_types::{BigEndianHash, H256, U256};
use evm_arithmetization::generation::{GenerationInputs, TrieInputs};
use evm_arithmetization::proof::{BlockHashes, BlockMetadata, TrieRoots};
use evm_arithmetization::prover::prove;
use evm_arithmetization::testing_utils::{
    init_logger, preinitialized_state, preinitialized_state_with_updated_storage,
};
use evm_arithmetization::verifier::verify_proof;
use evm_arithmetization::{AllStark, Node, StarkConfig};
use mpt_trie::partial_trie::{HashedPartialTrie, PartialTrie};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use rand::random;
use smt_trie::code::hash_bytecode_u256;
use smt_trie::utils::hashout2u;

type F = GoldilocksField;
const D: usize = 2;
type C = PoseidonGoldilocksConfig;

/// Add a new Global Exit Root to the state trie.
#[test]
fn test_global_exit_root() -> anyhow::Result<()> {
    init_logger();

    let all_stark = AllStark::<F, D>::default();
    let config = StarkConfig::standard_fast_config();

    let block_metadata = BlockMetadata {
        block_timestamp: 1.into(),
        ..BlockMetadata::default()
    };

    let state_smt = preinitialized_state();
    let transactions_trie = HashedPartialTrie::from(Node::Empty);
    let receipts_trie = HashedPartialTrie::from(Node::Empty);

    let mut contract_code = HashMap::new();
    contract_code.insert(hash_bytecode_u256(vec![]), vec![]);

    let global_exit_roots = vec![(U256(random()), H256(random()))];

    let expected_smt_after =
        preinitialized_state_with_updated_storage(&block_metadata, &global_exit_roots);

    let trie_roots_after = TrieRoots {
        state_root: H256::from_uint(&hashout2u(expected_smt_after.root)),
        transactions_root: transactions_trie.hash(),
        receipts_root: receipts_trie.hash(),
    };

    let inputs = GenerationInputs {
        signed_txn: None,
        withdrawals: vec![],
        global_exit_roots,
        tries: TrieInputs {
            state_smt: state_smt.serialize(),
            transactions_trie,
            receipts_trie,
        },
        trie_roots_after,
        contract_code,
        checkpoint_state_trie_root: HashedPartialTrie::from(Node::Empty).hash(),
        block_metadata,
        txn_number_before: 0.into(),
        gas_used_before: 0.into(),
        gas_used_after: 0.into(),
        block_hashes: BlockHashes {
            prev_hashes: vec![H256::default(); 256],
            cur_hash: H256::default(),
        },
    };

    let mut timing = TimingTree::new("prove", log::Level::Debug);
    let proof = prove::<F, C, D>(&all_stark, &config, inputs, &mut timing, None)?;
    timing.filter(Duration::from_millis(100)).print();

    verify_proof(&all_stark, proof, &config)
}
