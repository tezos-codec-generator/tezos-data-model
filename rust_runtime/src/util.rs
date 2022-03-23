use crate::parse::error::ConvError;

pub fn hex_of_bytes(bytes: &[u8]) -> String {
    let mut hex: String = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let word: String = format!("{:02x}", byte);
        hex.push_str(&word);
    }
    return hex;
}

pub fn bytes_of_hex<T: AsRef<str>>(src: &T) -> Result<Vec<u8>, ConvError<()>> {
    let src = src.as_ref();
    if src.is_empty() {
        return Ok(Vec::new());
    }

    let _l = src.len();

    if _l % 2 != 0 {
        return Err(ConvError::ParityError(()));
    }

    let n = _l / 2;

    let mut dst = Vec::with_capacity(n);

    for ix in 0..n {
        match u8::from_str_radix(&src[ix * 2..(ix + 1) * 2], 16) {
            Ok(word) => dst.push(word),
            Err(_) => return Err(ConvError::HexError(())),
        }
    }
    Ok(dst)
}