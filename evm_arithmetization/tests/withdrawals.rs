use std::collections::HashMap;
use std::time::Duration;

use env_logger::{try_init_from_env, Env, DEFAULT_FILTER_ENV};
use ethereum_types::{Address, BigEndianHash, H160, H256, U256};
use evm_arithmetization::generation::mpt::AccountRlp;
use evm_arithmetization::generation::{GenerationInputs, TrieInputs};
use evm_arithmetization::proof::{BlockHashes, BlockMetadata, TrieRoots};
use evm_arithmetization::prover::prove;
use evm_arithmetization::verifier::verify_proof;
use evm_arithmetization::{AllStark, Node, StarkConfig};
use mpt_trie::partial_trie::{HashedPartialTrie, PartialTrie};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::config::PoseidonGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use rand::random;
use smt_trie::code::hash_bytecode_u256;
use smt_trie::db::{Db, MemoryDb};
use smt_trie::keys::{key_balance, key_code, key_code_length, key_nonce, key_storage};
use smt_trie::smt::Smt;
use smt_trie::utils::hashout2u;

type F = GoldilocksField;
const D: usize = 2;
type C = PoseidonGoldilocksConfig;

/// Execute 0 txns and 1 withdrawal.
#[test]
fn test_withdrawals() -> anyhow::Result<()> {
    init_logger();

    let all_stark = AllStark::<F, D>::default();
    let config = StarkConfig::standard_fast_config();

    let block_metadata = BlockMetadata::default();

    let state_smt_before = Smt::<MemoryDb>::default();
    let transactions_trie = HashedPartialTrie::from(Node::Empty);
    let receipts_trie = HashedPartialTrie::from(Node::Empty);

    let mut contract_code = HashMap::new();
    contract_code.insert(hash_bytecode_u256(vec![]), vec![]);

    // Just one withdrawal.
    let withdrawals = vec![(H160(random()), U256(random()))];

    let state_smt_after = {
        let mut smt = Smt::<MemoryDb>::default();
        let account = AccountRlp {
            balance: withdrawals[0].1,
            ..AccountRlp::default()
        };
        set_account(&mut smt, withdrawals[0].0, &account, &HashMap::new());
        smt
    };

    let trie_roots_after = TrieRoots {
        state_root: H256::from_uint(&hashout2u(state_smt_after.root)),
        transactions_root: transactions_trie.hash(),
        receipts_root: receipts_trie.hash(),
    };

    let inputs = GenerationInputs {
        signed_txn: None,
        withdrawals,
        tries: TrieInputs {
            state_smt: state_smt_before.serialize(),
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

fn init_logger() {
    let _ = try_init_from_env(Env::default().filter_or(DEFAULT_FILTER_ENV, "info"));
}
fn set_account<D: Db>(
    smt: &mut Smt<D>,
    addr: Address,
    account: &AccountRlp,
    storage: &HashMap<U256, U256>,
) {
    smt.set(key_balance(addr), account.balance);
    smt.set(key_nonce(addr), account.nonce);
    smt.set(key_code(addr), account.code_hash);
    smt.set(key_code_length(addr), account.code_length);
    for (&k, &v) in storage {
        smt.set(key_storage(addr, k), v);
    }
}
