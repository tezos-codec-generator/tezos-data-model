extern crate faster_hex;
use crate::parse::error::ConvError;

use faster_hex::{hex_check_fallback, hex_decode_unchecked};

pub fn hex_of_bytes(bytes: &[u8]) -> String {
    let mut hex: String = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let word: String = format!("{:02x}", byte);
        hex.push_str(&word);
    }
    return hex;
}

/// Wrapper around [`hex_decode`] from `faster-hex`
pub fn bytes_of_hex<T: AsRef<[u8]>>(src: &T) -> Result<Vec<u8>, ConvError<()>> {
    let src = src.as_ref();
    if src.is_empty() {
        return Ok(Vec::new());
    }

    let _l = src.len();

    if _l & 1 != 0 {
        return Err(ConvError::ParityError(()));
    }

    let mut dst = Vec::with_capacity(_l >> 1);

    if !hex_check_fallback(src) {
        return Err(ConvError::HexError(()));
    }

    hex_decode_unchecked(src, &mut dst);
    Ok(dst)
}