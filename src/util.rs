//! Various utility functions

pub const U32_SIZE: usize = size_of::<i32>();

// Number deserializing functions. Each function will deserialize a number from a byte slice and
// panic if the slice is the wrong length.

pub fn u32_from_bytes(bytes: &[u8]) -> u32 {
    u32::from_le_bytes(bytes.try_into().expect("slice with incorrect length"))
}

// Number serializing functions. Each function will serialize a number into a byte array.

pub fn bytes_from_u32(u: u32) -> [u8; U32_SIZE] {
    u.to_le_bytes()
}
