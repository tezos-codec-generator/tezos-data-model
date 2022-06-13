use crate::error::ConvError;
use std::fmt::Write;

/// Formats a sequence of bytes as a `String` containing a hexadecimal blob
///
/// # Examples
///
/// ```
/// # use rust_runtime::util::hex_of_bytes;
/// assert_eq!(hex_of_bytes(vec![0xde,0xad,0xbe,0xef]), String::from("deadbeef"));
/// ```
#[must_use]
pub fn hex_of_bytes<T>(val: T) -> String
where
    T: AsRef<[u8]>,
{
    let bytes = val.as_ref();
    let mut hex: String = String::with_capacity(bytes.len() * 2);
    write_all_hex(bytes, &mut hex).unwrap();
    hex
}

pub(crate) fn write_all_hex(bytes: &[u8], tgt: &mut impl Write) -> std::fmt::Result {
    for &byte in bytes {
        write!(tgt, "{byte:02x}")?
    }
    Ok(())
}

/// Attempt to parse a string-like type as a hexadecimal blob, returning
/// the sequence of bytes encoded if it is a valid hex-string.
///
/// # Examples
///
/// ```
/// # use rust_runtime::util::bytes_of_hex;
/// assert_eq!(Ok(vec![0xde,0xad,0xbe,0xef]), bytes_of_hex("deadbeef"));
/// ```
///
pub fn bytes_of_hex<'a, T>(src: &'a T) -> Result<Vec<u8>, ConvError<&'a str>>
where
    T: AsRef<str> + ?Sized,
{
    let src: &'a str = src.as_ref();
    if src.is_empty() {
        return Ok(Vec::new());
    }

    let _l = src.len();

    if _l % 2 != 0 {
        return Err(ConvError::ParityError(src));
    }

    let n = _l / 2;

    let mut dst = Vec::with_capacity(n);

    for ix in 0..n {
        match u8::from_str_radix(&src[ix * 2..(ix + 1) * 2], 16) {
            Ok(word) => dst.push(word),
            Err(_) => return Err(ConvError::HexError(src)),
        }
    }
    Ok(dst)
}
