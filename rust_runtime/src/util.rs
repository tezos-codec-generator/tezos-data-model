pub fn hex_of_bytes(bytes: &[u8]) -> String {
    let mut hex : String = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        let word : String = format!("{:02x}", byte);
        hex.push_str(&word);
    }
    return hex;
}