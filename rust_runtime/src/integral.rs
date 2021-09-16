use crate::parse::byteparser::ByteParser;
use crate::conv::{ToBinary, FromBinary, Encode, Decode};

pub fn decode_u8(input : &str) -> u8 {
    let p = ByteParser::parse(input);
    p.get_uint8().unwrap()
}

impl ToBinary for u8 {
    fn bin_encode(&self) -> String {
        format!("{:02x}", self)
    }
}

impl FromBinary for u8 {
    fn bin_decode(inp: &str) -> Self {
        decode_u8(inp)
    }
}

impl Encode<String> for u8 {
    fn encode(&self) -> String {
        self.bin_encode()
    }
}

impl Decode<u8> for str {
    fn decode(&self) -> u8 {
        u8::bin_decode(self)
    }
}

impl Decode<u8> for [u8] {
    fn decode(&self) -> u8 {
        self[0]
    }
}

impl Decode<u8> for ByteParser {
    fn decode(&self) -> u8 {
        self.get_uint8().unwrap()
    }
}