use ethereum_types::H256;
use keccak_hash::keccak;

pub(crate) fn hash(bytes: &[u8]) -> H256 {
    H256::from(keccak(bytes).0)
}

pub(crate) fn update_val_if_some<T>(target: &mut T, opt: Option<T>) {
    if let Some(new_val) = opt {
        *target = new_val;
    }
}

pub(crate) fn optional_field<T: std::fmt::Debug>(label: &str, value: Option<T>) -> String {
    value.map_or(String::new(), |v| format!("{}: {:?}\n", label, v))
}

pub(crate) fn optional_field_hex<T: std::fmt::UpperHex>(label: &str, value: Option<T>) -> String {
    value.map_or(String::new(), |v| format!("{}: 0x{:064X}\n", label, v))
}
