/// Access lists for addresses and storage keys.
/// The access list is stored in a sorted linked list in SEGMENT_ACCESSED_ADDRESSES for addresses and
/// SEGMENT_ACCESSED_STORAGE_KEYS segment for storage keys. The length of
/// the segments is stored in the global metadata.
/// Both arrays are stored in the kernel memory (context=0).
/// Searching and inserting is done by guessing the predecessor in the list.
/// If the address/storage key isn't found in the array, it is inserted at the end.

// Initialize the set of accessed addresses and storage keys with an empty list of the form (@U256_MAX)⮌
// which is written as [@U256_MAX, @SEGMENT_ACCESSED_ADDRESSES] in SEGMENT_ACCESSED_ADDRESSES
// and as [@U256_MAX, _, _, @SEGMENT_ACCESSED_STORAGE_KEYS] in SEGMENT_ACCESSED_STORAGE_KEYS.
// Initialize SEGMENT_ACCESSED_ADDRESSES
global init_access_lists_original:
    // stack: (empty)
    // Store @U256_MAX at the beggining of the segment
    PUSH @SEGMENT_ACCESSED_ADDRESSES // ctx == virt == 0
    DUP1
    PUSH @U256_MAX
    MSTORE_GENERAL
    // Store @SEGMENT_ACCESSED_ADDRESSES at address 1
    %increment
    DUP1
    PUSH @SEGMENT_ACCESSED_ADDRESSES
    MSTORE_GENERAL

    // Store the segment scaled length
    %increment
    %mstore_global_metadata(@GLOBAL_METADATA_ACCESSED_ADDRESSES_LEN)
    // stack: (empty)

    // Initialize SEGMENT_ACCESSED_STORAGE_KEYS
    // Store @U256_MAX at the beggining of the segment
    PUSH @SEGMENT_ACCESSED_STORAGE_KEYS // ctx == virt == 0
    DUP1
    PUSH @U256_MAX
    MSTORE_GENERAL
    // Store @SEGMENT_ACCESSED_STORAGE_KEYS at address 3
    %add_const(3)
    DUP1
    PUSH @SEGMENT_ACCESSED_STORAGE_KEYS
    MSTORE_GENERAL
    
    // Store the segment scaled length
    %increment
    %mstore_global_metadata(@GLOBAL_METADATA_ACCESSED_STORAGE_KEYS_LEN)
    JUMP

// Methods for storage and addresses access lists. The acesses are tracked through a counter in 
// linked_lists. We need to make sure that all accounts in the linked list have counter 0.
global init_access_lists:
    // stack: retdest
    %init_accounts_list
    %init_storage_list
    JUMP

%macro init_accounts_list
    // stack: retdest
    PUSH @SEGMENT_ACCOUNTS_LINKED_LIST
    DUP1 %add_const(2)
    // stack: init_counter_ptr, init_ptr, retdest
    MLOAD_GENERAL %assert_zero
    // stack: init_ptr, retdest
%%init_account_loop:
    %add_const(3) MLOAD_GENERAL
    // stack: next_ptr, retdest
    DUP1 MLOAD_GENERAL
    // stack: next_addr, next_ptr, retdest
    PUSH @U256_MAX EQ %jumpi(%%end_init_accounts_loop)
    // stack: next_ptr, retdest
    DUP1 %add_const(2)
    // stack: next_counter_ptr, next_ptr, retdest
    PUSH 0 MSTORE_GENERAL
    // stack: next_ptr, retdest
    %jump(%%init_account_loop)
%%end_init_accounts_loop:
    // stack: final_ptr, retdest
    POP
    JUMP
%endmacro

%macro init_storage_list
    // stack: retdest
    PUSH @SEGMENT_STORAGE_LINKED_LIST
    DUP1 %add_const(3)
    // stack: init_counter_ptr, init_ptr, retdest
    MLOAD_GENERAL %assert_zero
    // stack: init_ptr, retdest
%%init_storage_loop:
    %add_const(4) MLOAD_GENERAL
    // stack: next_ptr, retdest
    DUP1 MLOAD_GENERAL
    // stack: next_addr, next_ptr, retdest
    PUSH @U256_MAX EQ %jumpi(%%end_init_storage_loop)
    // stack: next_ptr, retdest
    DUP1 %add_const(3)
    // stack: next_counter_ptr, next_ptr, retdest
    PUSH 0 MSTORE_GENERAL
    // stack: next_ptr, retdest
    %jump(%%init_storage_loop)
%%end_init_storage_loop:
    // stack: final_ptr, retdest
    POP
    JUMP
%endmacro

%macro init_access_lists
    PUSH %%after
    %jump(init_access_lists)
%%after:
%endmacro

%macro insert_accessed_addresses
    %stack (addr) -> (addr, %%after)
    %jump(insert_accessed_addresses)
%%after:
    // stack: cold_access
%endmacro

%macro insert_accessed_addresses_no_return
    %insert_accessed_addresses
    POP
%endmacro

// Multiply the ptr at the top of the stack by 2
// and abort if 2*ptr - @SEGMENT_ACCESSED_ADDRESSES >= @GLOBAL_METADATA_ACCESSED_ADDRESSES_LEN
// In this way ptr must be pointing to the begining of a node.
%macro get_valid_addr_ptr
    // stack: ptr
    %mul_const(2)
    PUSH @SEGMENT_ACCESSED_ADDRESSES
    DUP2
    SUB
    %assert_lt_const(@GLOBAL_METADATA_ACCESSED_ADDRESSES_LEN)
    // stack: 2*ptr
%endmacro

global insert_accessed_addresses:
    // stack: addr, retdest
    PUSH 0 DUP2 %addr_to_state_key
    // stack: addr_key, payload_ptr, addr, retdest
    %insert_account_to_linked_list
    // stack: account_found, cold_access, account_ptr, addr
    %stack (account_found, cold_access, account_ptr, addr, retdest) -> (addr, retdest, cold_access)
    %journal_add_account_loaded
    // stack: retdest, cold_access
    JUMP

/// Inserts the address into the access list if it is not already present.
/// Return 1 if the address was inserted, 0 if it was already present.
global insert_accessed_addresses_original:
    // stack: addr, retdest
    PROVER_INPUT(access_lists::address_insert)
    // stack: pred_ptr/2, addr, retdest
    %get_valid_addr_ptr
    // stack: pred_ptr, addr, retdest
    DUP1
    MLOAD_GENERAL
    // stack: pred_addr, pred_ptr, addr, retdest
    // If pred_add < addr OR pred_ptr == @SEGMENT_ACCESSED_ADDRESSES
    DUP2
    %eq_const(@SEGMENT_ACCESSED_ADDRESSES)
    // pred_ptr == start, pred_addr, pred_ptr, addr, retdest
    DUP2 DUP5 GT
    // addr > pred_addr, pred_ptr == start, pred_addr, pred_ptr, addr, retdest
    OR
    // (addr > pred_addr) || (pred_ptr == start), pred_addr, pred_ptr, addr, retdest
    %jumpi(insert_new_address)
    // Here, addr <= pred_addr. Assert that `addr == pred_addr`.
    // stack: pred_addr, pred_ptr, addr, retdest
    DUP3
    // stack: addr, pred_addr, pred_ptr, addr, retdest
    %assert_eq
    
    // stack: pred_ptr, addr, retdest
    // Check that this is not a deleted node
    %increment
    MLOAD_GENERAL
    %jump_neq_const(@U256_MAX, address_found)
    // We should have found the address.
    PANIC
address_found:
    // The address was already in the list
    %stack (addr, retdest) -> (retdest, 0) // Return 0 to indicate that the address was already present.
    JUMP

insert_new_address:
    // stack: pred_addr, pred_ptr, addr, retdest
    POP
    // get the value of the next address
    %increment
    // stack: next_ptr_ptr, addr, retdest
    %mload_global_metadata(@GLOBAL_METADATA_ACCESSED_ADDRESSES_LEN)
    DUP2
    MLOAD_GENERAL
    // stack: next_ptr, new_ptr, next_ptr_ptr, addr, retdest
    // Check that this is not a deleted node
    DUP1
    %eq_const(@U256_MAX)
    %assert_zero
    DUP1
    MLOAD_GENERAL
    // stack: next_val, next_ptr, new_ptr, next_ptr_ptr, addr, retdest
    DUP5
    // Here, (addr > pred_addr) || (pred_ptr == @SEGMENT_ACCESSED_STORAGE_KEYS).
    // We should have (addr < next_val), meaning the new value can be inserted between pred_ptr and next_ptr.
    %assert_lt
    // stack: next_ptr, new_ptr, next_ptr_ptr, addr, retdest
    SWAP2
    DUP2
    // stack: new_ptr, next_ptr_ptr, new_ptr, next_ptr, addr, retdest
    MSTORE_GENERAL
    // stack: new_ptr, next_ptr, addr, retdest
    DUP1
    DUP4
    MSTORE_GENERAL
    // stack: new_ptr, next_ptr, addr, retdest
    %increment
    DUP1
    // stack: new_next_ptr, new_next_ptr, next_ptr, addr, retdest
    SWAP2
    MSTORE_GENERAL
    // stack: new_next_ptr, addr, retdest
    %increment
    %mstore_global_metadata(@GLOBAL_METADATA_ACCESSED_ADDRESSES_LEN)
    // stack: addr, retdest
    %journal_add_account_loaded
    PUSH 1
    SWAP1
    JUMP

/// Remove the address from the access list.
/// Panics if the address is not in the access list.
/// Otherwise it guesses the node before the address (pred)
/// such that (pred)->(next)->(next_next), where the (next) node
/// stores the address. It writes the link (pred)->(next_next)
/// and (next) is marked as deleted by writting U256_MAX in its 
/// next node pointer.
global remove_accessed_addresses_original:
    // stack: addr, retdest
    PROVER_INPUT(access_lists::address_remove)
    // stack: pred_ptr/2, addr, retdest
    %get_valid_addr_ptr
    // stack: pred_ptr, addr, retdest
    %increment
    // stack: next_ptr_ptr, addr, retdest
    DUP1
    MLOAD_GENERAL
    // stack: next_ptr, next_ptr_ptr, addr, retdest
    DUP1
    MLOAD_GENERAL
    // stack: next_val, next_ptr, next_ptr_ptr, addr, retdest
    DUP4
    %assert_eq
    // stack: next_ptr, next_ptr_ptr, addr, retdest
    %increment
    // stack: next_next_ptr_ptr, next_ptr_ptr, addr, retdest
    DUP1
    MLOAD_GENERAL
    // stack: next_next_ptr, next_next_ptr_ptr, next_ptr_ptr, addr, retdest
    SWAP1
    PUSH @U256_MAX
    MSTORE_GENERAL
    // stack: next_next_ptr, next_ptr_ptr, addr, retdest
    MSTORE_GENERAL
    POP
    JUMP

global remove_accessed_addresses:
    // stack: addr, retdest
    // Find the account pointer in the linked list.
    %read_accounts_linked_list
    // stack: cold_access, account_ptr, retdest
    POP
    DUP1 %assert_nonzero
    // Since we call the journal whether the access was warm or cold,
    // we do not simpoly set the counter to 0, but rather decrement it.
    // We actually need to remove 2 to the counter because we just
    // increased it when searching for the account.
    %add_const(2)
    // stack: counter_ptr, retdest
    DUP1 MLOAD_GENERAL
    // stack: counter, counter_ptr. retdest
    %assert_gt_const(2)
    %sub_const(2) MSTORE_GENERAL
    // stack: retdest
    JUMP

%macro insert_accessed_storage_keys
    %stack (addr, slot) -> (addr, slot, %%after)
    %jump(insert_accessed_storage_keys)
%%after:
    // stack: cold_access, value_ptr
%endmacro

// Multiply the ptr at the top of the stack by 4
// and abort if 4*ptr - SEGMENT_ACCESSED_STORAGE_KEYS >= @GLOBAL_METADATA_ACCESSED_STORAGE_KEYS_LEN
// In this way ptr must be pointing to the beginning of a node.
%macro get_valid_storage_ptr
    // stack: ptr
    %mul_const(4)
    PUSH @SEGMENT_ACCESSED_STORAGE_KEYS
    DUP2
    SUB
    %assert_lt_const(@GLOBAL_METADATA_ACCESSED_STORAGE_KEYS_LEN)
    // stack: 2*ptr
%endmacro

global insert_accessed_storage_keys:
    // stack: addr, slot, retdest
    PUSH 0
    DUP3 %slot_to_storage_key
    DUP3 %addr_to_state_key
    // stack: addr_key, slot_key, addr, slot, retdest
    %insert_slot
    // stack: cold_access, storage_ptr, addr, slot, retdest
    %stack (cold_access, storage_ptr, addr, slot, retdest) -> (addr, slot, retdest, cold_access, storage_ptr)
    %journal_add_storage_loaded
    // stack: retdest, cold_access, storage_ptr
    JUMP
    

/// Inserts the storage key into the access list if it is not already present.
/// Return `1, value_ptr` if the storage key was inserted, `0, value_ptr` if it was already present.
/// Callers to this function must ensure the original storage value is stored at `value_ptr`.
global insert_accessed_storage_keys_original:
    // stack: addr, key, retdest
    PROVER_INPUT(access_lists::storage_insert)
    // stack: pred_ptr/4, addr, key, retdest
    %get_valid_storage_ptr
    // stack: pred_ptr, addr, key, retdest
    DUP1
    MLOAD_GENERAL
    DUP1
    // stack: pred_addr, pred_addr, pred_ptr, addr, key, retdest
    DUP4 GT
    DUP3 %eq_const(@SEGMENT_ACCESSED_STORAGE_KEYS)
    ADD // OR
    %jumpi(insert_storage_key)
    // stack: pred_addr, pred_ptr, addr, key, retdest
    // We know that addr <= pred_addr. It must hold that pred_addr == addr.
    DUP3
    %assert_eq
    // stack: pred_ptr, addr, key, retdest
    DUP1
    %increment
    MLOAD_GENERAL
    // stack: pred_key, pred_ptr, addr, key, retdest
    DUP1 DUP5
    GT
    // stack: key > pred_key, pred_key, pred_ptr, addr, key, retdest
    %jumpi(insert_storage_key)
    // stack: pred_key, pred_ptr, addr, key, retdest
    DUP4
    // We know that key <= pred_key. It must hold that pred_key == key.
    %assert_eq
    // stack: pred_ptr, addr, key, retdest
    // Check that this is not a deleted node
    DUP1
    %add_const(3)
    MLOAD_GENERAL
    %jump_neq_const(@U256_MAX, storage_key_found)
    // The storage key is not in the list.
    PANIC

storage_key_found:
    // The address was already in the list
    // stack: pred_ptr, addr, key, retdest
    %add_const(2)
    %stack (value_ptr, addr, key, retdest) -> (retdest, 0, value_ptr) // Return 0 to indicate that the address was already present.
    JUMP

insert_storage_key:
    // stack: pred_addr or pred_key, pred_ptr, addr, key, retdest
    POP
    // Insert a new storage key
    // stack: pred_ptr, addr, key, retdest
    // get the value of the next address
    %add_const(3)
    // stack: next_ptr_ptr, addr, key, retdest
    %mload_global_metadata(@GLOBAL_METADATA_ACCESSED_STORAGE_KEYS_LEN)
    DUP2
    MLOAD_GENERAL
    // stack: next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    // Check that this is not a deleted node
    DUP1
    %eq_const(@U256_MAX)
    %assert_zero
    DUP1
    MLOAD_GENERAL
    // stack: next_val, next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    DUP5
    // Check that addr < next_val OR (next_val == addr AND key < next_key)
    DUP2 DUP2
    LT
    // stack: addr < next_val, addr, next_val, next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    SWAP2
    EQ
    // stack: next_val == addr, addr < next_val, next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    DUP3 %increment
    MLOAD_GENERAL
    DUP8
    LT
    // stack: next_key > key, next_val == addr, addr < next_val, next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    AND
    OR
    %assert_nonzero
    // stack: next_ptr, new_ptr, next_ptr_ptr, addr, key, retdest
    SWAP2
    DUP2
    MSTORE_GENERAL
    // stack: new_ptr, next_ptr, addr, key, retdest
    DUP1
    DUP4
    MSTORE_GENERAL // store addr
    // stack: new_ptr, next_ptr, addr, key, retdest
    %increment
    DUP1
    // stack: new_ptr+1, new_ptr+1, next_ptr, addr, key, retdest
    DUP5
    // stack: key, new_ptr+1, new_ptr+1, next_ptr, addr, key, retdest
    MSTORE_GENERAL // store key
    // stack: new_ptr+1, next_ptr, addr, key, retdest
    %increment
    DUP1
    // stack: new_ptr+2, value_ptr, next_ptr, addr, key, retdest
    %increment
    DUP1
    // stack: new_next_ptr, new_next_ptr, value_ptr, next_ptr, addr, key, retdest
    SWAP3
    // stack: next_ptr, new_next_ptr, value_ptr, new_next_ptr, addr, key, retdest
    MSTORE_GENERAL
    // stack: value_ptr, new_next_ptr, addr, key, retdest
    SWAP1
    // stack: new_next_ptr, value_ptr, addr, key, retdest
    %increment
    %mstore_global_metadata(@GLOBAL_METADATA_ACCESSED_STORAGE_KEYS_LEN)
    // stack: value_ptr, addr, key, retdest
    %stack (value_ptr, addr, key, retdest) -> (addr, key, retdest, 1, value_ptr)
    %journal_add_storage_loaded
    JUMP

/// Remove the storage key and its value from the access list.
/// Panics if the key is not in the list.
global remove_accessed_storage_keys_original:
    // stack: addr, key, retdest
    PROVER_INPUT(access_lists::storage_remove)
    // stack: pred_ptr/4, addr, key, retdest
    %get_valid_storage_ptr
    // stack: pred_ptr, addr, key, retdest
    %add_const(3)
    // stack: next_ptr_ptr, addr, key, retdest
    DUP1
    MLOAD_GENERAL
    // stack: next_ptr, next_ptr_ptr, addr, key, retdest
    DUP1
    %increment
    MLOAD_GENERAL
    // stack: next_key, next_ptr, next_ptr_ptr, addr, key, retdest
    DUP5
    EQ
    DUP2
    MLOAD_GENERAL
    // stack: next_addr, next_key == key, next_ptr, next_ptr_ptr, addr, key, retdest
    DUP5
    EQ
    MUL // AND
    // stack: next_addr == addr AND next_key == key, next_ptr, next_ptr_ptr, addr, key, retdest
    %assert_nonzero
    // stack: next_ptr, next_ptr_ptr, addr, key, retdest
    %add_const(3)
    // stack: next_next_ptr_ptr, next_ptr_ptr, addr, key, retdest
    DUP1
    MLOAD_GENERAL
    // stack: next_next_ptr, next_next_ptr_ptr, next_ptr_ptr, addr, key, retdest
    SWAP1
    PUSH @U256_MAX
    MSTORE_GENERAL
    // stack: next_next_ptr, next_ptr_ptr, addr, key, retdest
    MSTORE_GENERAL
    %pop2
    JUMP

global remove_accessed_storage_keys:
    // stack: addr, slot, retdest
    %read_slot_linked_list
    // stack: slot_ptr, retdest
    DUP1 %assert_nonzero
    // stack: slot_ptr, retdest
    %add_const(3) DUP1 MLOAD_GENERAL
    // stack: slot_ctr, slot_ctr_ptr, retdest
    DUP1 %assert_gt_const(2)
    %sub_const(2) MSTORE_GENERAL
    // stack: retdest
    JUMP
