use crate::conv::{Decode, Encode, FromBinary, ToBinary};
use crate::parse::byteparser::{ByteParser, ToParser};

pub mod integral {
    use super::*;

    pub fn decode_u8(input: &str) -> u8 {
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

    impl<T> Decode<T> for u8
    where
        T: ToParser
    {
        fn decode(inp: T) -> Self {
            let p = inp.to_parser();
            p.get_uint8().unwrap()
        }
    }
}

pub fn decode_bool(input: &str) -> bool {
    let p = ByteParser::parse(input);
    p.get_bool().unwrap()
}

impl ToBinary for bool {
    fn bin_encode(&self) -> String {
        match self {
            &true => String::from("ff"),
            &false => String::from("00"),
        }
    }
}

impl FromBinary for bool {
    fn bin_decode(inp: &str) -> Self {
        decode_bool(inp)
    }
}

impl Encode<String> for bool {
    fn encode(&self) -> String {
        self.bin_encode()
    }
}

impl<T> Decode<T> for bool
where
    T: ToParser
{
    fn decode(inp: T) -> Self {
        let p = inp.to_parser();
        p.get_bool().unwrap()
    }
}