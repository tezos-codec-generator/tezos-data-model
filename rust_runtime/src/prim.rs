use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;

pub mod integral {
    use super::*;

    impl Encode<String> for u8 {
        fn encode(&self) -> String {
            format!("{:02x}", *self)
        }
    }

    impl Decode for u8 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_uint8().unwrap()
        }
    }

    impl Encode<String> for i8 {
        fn encode(&self) -> String {
            format!("{:02x}", *self)
        }
    }

    impl Decode for i8 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_int8().unwrap()
        }
    }
}

impl Encode<String> for bool {
    fn encode(&self) -> String {
        match self {
            &true => String::from("ff"),
            &false => String::from("00"),
        }
    }
}

impl Decode for bool {
    fn decode<U: ToParser>(inp: U) -> Self {
        let p = inp.to_parser();
        p.get_bool().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const U8_CASES: [(u8, &'static str); 5] = [
        (0x00, "00"),
        (0x01, "01"),
        (0x7f, "7f"),
        (0x80, "80"),
        (0xff, "ff"),
    ];

    const I8_CASES: [(i8, &'static str); 5] = [
        (0x00, "00"),
        (0x01, "01"),
        (0x7f, "7f"),
        (-128, "80"),
        (-1, "ff"),
    ];

    #[test]
    fn test_uint8_encode() {
        for (u, enc) in U8_CASES.iter() {
            assert_eq!(enc.to_owned(), u.encode());
        }
    }

    #[test]
    fn test_uint8_decode() {
        for (u, enc) in U8_CASES.iter() {
            assert_eq!(u8::decode(enc.to_owned()), *u);
        }
    }

    #[test]
    fn test_int8_encode() {
        for (i, enc) in I8_CASES.iter() {
            assert_eq!(enc.to_owned(), i.encode());
        }
    }

    #[test]
    fn test_int8_decode() {
        for (i, enc) in I8_CASES.iter() {
            assert_eq!(i8::decode(enc.to_owned()), *i);
        }
    }
}

