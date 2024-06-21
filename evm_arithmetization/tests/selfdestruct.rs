use std::collections::HashMap;
use std::str::FromStr;
use std::time::Duration;

use ethereum_types::{Address, BigEndianHash, H160, H256, U256};
use evm_arithmetization::generation::mpt::{AccountRlp, LegacyReceiptRlp};
use evm_arithmetization::generation::{GenerationInputs, TrieInputs};
use evm_arithmetization::proof::{BlockHashes, BlockMetadata, TrieRoots};
use evm_arithmetization::prover::prove;
use evm_arithmetization::testing_utils::{
    eth_to_wei, init_logger, preinitialized_state, preinitialized_state_with_updated_storage,
    set_account,
};
use evm_arithmetization::verifier::verify_proof;
use evm_arithmetization::{AllStark, Node, StarkConfig};
use hex_literal::hex;
use mpt_trie::nibbles::Nibbles;
use mpt_trie::partial_trie::{HashedPartialTrie, PartialTrie};
use plonky2::field::goldilocks_field::GoldilocksField;
use plonky2::plonk::config::KeccakGoldilocksConfig;
use plonky2::util::timing::TimingTree;
use smt_trie::code::hash_bytecode_u256;
use smt_trie::utils::hashout2u;

type F = GoldilocksField;
const D: usize = 2;
type C = KeccakGoldilocksConfig;

/// Test a simple selfdestruct.
#[test]
fn test_selfdestruct() -> anyhow::Result<()> {
    init_logger();

    let all_stark = AllStark::<F, D>::default();
    let config = StarkConfig::standard_fast_config();

    let beneficiary = hex!("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
    let sender = hex!("5eb96AA102a29fAB267E12A40a5bc6E9aC088759");
    let to = hex!("a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0");

    let sender_account_before = AccountRlp {
        nonce: 5.into(),
        balance: eth_to_wei(100_000.into()),
        ..Default::default()
    };
    let code = vec![
        0x32, // ORIGIN
        0xFF, // SELFDESTRUCT
    ];
    let to_account_before = AccountRlp {
        nonce: 12.into(),
        balance: eth_to_wei(10_000.into()),
        code_hash: hash_bytecode_u256(code.clone()),
        ..Default::default()
    };

    let mut state_smt_before = preinitialized_state();
    set_account(
        &mut state_smt_before,
        H160(sender),
        &sender_account_before,
        &HashMap::new(),
    );
    set_account(
        &mut state_smt_before,
        H160(to),
        &to_account_before,
        &HashMap::new(),
    );

    let tries_before = TrieInputs {
        state_smt: state_smt_before.serialize(),
        transactions_trie: HashedPartialTrie::from(Node::Empty),
        receipts_trie: HashedPartialTrie::from(Node::Empty),
    };

    // Generated using a little py-evm script.
    let txn = hex!("f868050a831e848094a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0880de0b6b3a76400008025a09bab8db7d72e4b42cba8b117883e16872966bae8e4570582de6ed0065e8c36a1a01256d44d982c75e0ab7a19f61ab78afa9e089d51c8686fdfbee085a5ed5d8ff8");

    let block_metadata = BlockMetadata {
        block_beneficiary: Address::from(beneficiary),
        block_timestamp: 0x03e8.into(),
        block_number: 1.into(),
        block_difficulty: 0x020000.into(),
        block_random: H256::from_uint(&0x020000.into()),
        block_gaslimit: 0xff112233u32.into(),
        block_chain_id: 1.into(),
        block_base_fee: 0xa.into(),
        block_gas_used: 26002.into(),
        ..Default::default()
    };

    let contract_code = [
        (hash_bytecode_u256(code.clone()), code),
        (hash_bytecode_u256(vec![]), vec![]),
    ]
    .into();

    let expected_state_smt_after = {
        let mut smt = preinitialized_state_with_updated_storage(&block_metadata, &[]);
        let sender_account_after = AccountRlp {
            nonce: 6.into(),
            balance: eth_to_wei(110_000.into()) - 26_002 * 0xa,
            ..Default::default()
        };
        let to_account_after = AccountRlp {
            balance: U256::zero(),
            ..to_account_before
        };
        set_account(
            &mut smt,
            H160(sender),
            &sender_account_after,
            &HashMap::new(),
        );
        set_account(&mut smt, H160(to), &to_account_after, &HashMap::new());
        smt
    };

    let receipt_0 = LegacyReceiptRlp {
        status: true,
        cum_gas_used: 26002.into(),
        bloom: vec![0; 256].into(),
        logs: vec![],
    };
    let mut receipts_trie = HashedPartialTrie::from(Node::Empty);
    receipts_trie.insert(
        Nibbles::from_str("0x80").unwrap(),
        rlp::encode(&receipt_0).to_vec(),
    )?;
    let transactions_trie: HashedPartialTrie = Node::Leaf {
        nibbles: Nibbles::from_str("0x80").unwrap(),
        value: txn.to_vec(),
    }
    .into();

    let trie_roots_after = TrieRoots {
        state_root: H256::from_uint(&hashout2u(expected_state_smt_after.root)),
        transactions_root: transactions_trie.hash(),
        receipts_root: receipts_trie.hash(),
    };
    let inputs = GenerationInputs {
        signed_txn: Some(txn.to_vec()),
        withdrawals: vec![],
        global_exit_roots: vec![],
        tries: tries_before,
        trie_roots_after,
        contract_code,
        checkpoint_state_trie_root: HashedPartialTrie::from(Node::Empty).hash(),
        block_metadata,
        txn_number_before: 0.into(),
        gas_used_before: 0.into(),
        gas_used_after: 26002.into(),
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

#[test]
fn test_selfdestruct_with_storage() -> anyhow::Result<()> {
    init_logger();

    let all_stark = AllStark::<F, D>::default();
    let config = StarkConfig::standard_fast_config();

    let beneficiary = hex!("deadbeefdeadbeefdeadbeefdeadbeefdeadbeef");
    let sender = hex!("5eb96AA102a29fAB267E12A40a5bc6E9aC088759");
    let to = hex!("a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0");

    let sender_account_before = AccountRlp {
        nonce: 5.into(),
        balance: eth_to_wei(100_000.into()),
        ..Default::default()
    };
    let initcode = vec![
        0x42, // TIMESTAMP
        0x60, 0x01, // PUSH1 1
        0x80, // DUP1
        0x55, // SSTORE
        0x32, // ORIGIN
        0xFF, // SELFDESTRUCT
    ];
    let code = [
        vec![
            0x66, // PUSH7
        ],
        initcode,
        vec![
            0x5F, // PUSH0
            0x52, // MSTORE
            0x60, 0x07, // PUSH1 7
            0x60, 0x19, // PUSH1 25
            0x5F, // PUSH0
            0xF0, // CREATE
        ],
    ]
    .concat();
    let to_account_before = AccountRlp {
        nonce: 12.into(),
        balance: eth_to_wei(10_000.into()),
        code_hash: hash_bytecode_u256(code.clone()),
        ..Default::default()
    };

    let mut state_smt_before = preinitialized_state();
    set_account(
        &mut state_smt_before,
        H160(sender),
        &sender_account_before,
        &HashMap::new(),
    );
    set_account(
        &mut state_smt_before,
        H160(to),
        &to_account_before,
        &HashMap::new(),
    );

    let tries_before = TrieInputs {
        state_smt: state_smt_before.serialize(),
        transactions_trie: HashedPartialTrie::from(Node::Empty),
        receipts_trie: HashedPartialTrie::from(Node::Empty),
    };

    // Generated using a little py-evm script.
    let txn = hex!("f868050a831e848094a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0880de0b6b3a76400008025a09bab8db7d72e4b42cba8b117883e16872966bae8e4570582de6ed0065e8c36a1a01256d44d982c75e0ab7a19f61ab78afa9e089d51c8686fdfbee085a5ed5d8ff8");

    let block_metadata = BlockMetadata {
        block_beneficiary: Address::from(beneficiary),
        block_timestamp: 0x03e8.into(),
        block_number: 1.into(),
        block_difficulty: 0x020000.into(),
        block_random: H256::from_uint(&0x020000.into()),
        block_gaslimit: 0xff112233u32.into(),
        block_chain_id: 1.into(),
        block_base_fee: 0xa.into(),
        block_gas_used: 80131.into(),
        ..Default::default()
    };

    let contract_code = [
        (hash_bytecode_u256(code.clone()), code),
        (hash_bytecode_u256(vec![]), vec![]),
    ]
    .into();

    let value = eth_to_wei(1.into());
    let expected_state_smt_after = {
        let mut smt = preinitialized_state_with_updated_storage(&block_metadata, &[]);
        let sender_account_after = AccountRlp {
            nonce: sender_account_before.nonce + 1,
            balance: sender_account_before.balance - 80131 * 0xa - value,
            ..sender_account_before
        };
        let to_account_after = AccountRlp {
            nonce: to_account_before.nonce + 1,
            balance: to_account_before.balance + value,
            ..to_account_before
        };
        set_account(
            &mut smt,
            H160(sender),
            &sender_account_after,
            &HashMap::new(),
        );
        set_account(&mut smt, H160(to), &to_account_after, &HashMap::new());
        smt
    };

    let receipt_0 = LegacyReceiptRlp {
        status: true,
        cum_gas_used: 80131.into(),
        bloom: vec![0; 256].into(),
        logs: vec![],
    };
    let mut receipts_trie = HashedPartialTrie::from(Node::Empty);
    receipts_trie.insert(
        Nibbles::from_str("0x80").unwrap(),
        rlp::encode(&receipt_0).to_vec(),
    )?;
    let transactions_trie: HashedPartialTrie = Node::Leaf {
        nibbles: Nibbles::from_str("0x80").unwrap(),
        value: txn.to_vec(),
    }
    .into();

    let trie_roots_after = TrieRoots {
        state_root: H256::from_uint(&hashout2u(expected_state_smt_after.root)),
        transactions_root: transactions_trie.hash(),
        receipts_root: receipts_trie.hash(),
    };
    let inputs = GenerationInputs {
        signed_txn: Some(txn.to_vec()),
        withdrawals: vec![],
        tries: tries_before,
        trie_roots_after,
        contract_code,
        global_exit_roots: vec![],
        checkpoint_state_trie_root: HashedPartialTrie::from(Node::Empty).hash(),
        block_metadata,
        txn_number_before: 0.into(),
        gas_used_before: 0.into(),
        gas_used_after: 80131.into(),
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
