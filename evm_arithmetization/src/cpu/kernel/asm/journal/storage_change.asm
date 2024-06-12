// struct StorageChange { address, slot, prev_value }

%macro journal_add_storage_change
    %journal_add_3(@JOURNAL_ENTRY_STORAGE_CHANGE)
%endmacro

global revert_storage_change_original:
    // stack: entry_type, ptr, retdest
    POP
    %journal_load_3
    // stack: address, slot, prev_value, retdest
    DUP3 ISZERO %jumpi(delete)
    // stack: address, slot, prev_value, retdest
    %read_slot_linked_list
    // stack: value_ptr, prev_value, retdest
    DUP1 %assert_nonzero
    // stack: value_ptr, prev_value, retdest
    %mstore_trie_data
    JUMP

global revert_storage_change:
    // stack: entry_type, ptr, retdest
    POP
    %journal_load_3
    // stack: address, slot, prev_value, retdest
    DUP3 ISZERO %jumpi(delete)
    // stack: address, slot, prev_value, retdest
    %read_slot_linked_list
    // stack: value_ptr, prev_value, retdest
    DUP1 %assert_nonzero
    // stack: value_ptr, prev_value, retdest
    %mstore_trie_data
    JUMP

delete_original:
    // stack: address, slot, prev_value, retdest
    SWAP2 POP
    // stack: slot, address, retdest
    %slot_to_storage_key
    SWAP1 %addr_to_state_key
    // stack: addr_key, slot_key, retdest
    %jump(remove_slot)

delete:
    // stack: address, slot, prev_value, retdest
    SWAP2 POP
    // stack: slot, address, retdest
    %slot_to_storage_key
    SWAP1 %addr_to_state_key
    // stack: addr_key, slot_key, retdest
    %jump(remove_slot)

new_storage_root:
    // stack: new_storage_root_ptr, address, retdest
    DUP2 %mpt_read_state_trie
    // stack: account_ptr, new_storage_root_ptr, address, retdest

    // Update account with our new storage root pointer.
    %add_const(2)
    // stack: account_storage_root_ptr_ptr, new_storage_root_ptr, address, retdest
    %mstore_trie_data
    // stack: address, retdest
    POP JUMP
