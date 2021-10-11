use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;

pub mod integral {
    use super::*;

    impl Encode<String> for u8 {
        fn encode(&self) -> String {
            format!("{:02x}", *self)
        }
    }

    impl Encode<String> for i8 {
        fn encode(&self) -> String {
            format!("{:02x}", *self)
        }
    }

    impl Encode<String> for u16 {
        fn encode(&self) -> String {
            format!("{:04x}", *self)
        }
    }

    impl Encode<String> for i16 {
        fn encode(&self) -> String {
            format!("{:04x}", *self)
        }
    }

    impl Encode<String> for u32 {
        fn encode(&self) -> String {
            format!("{:08x}", *self)
        }
    }

    impl Encode<String> for i32 {
        fn encode(&self) -> String {
            format!("{:08x}", *self)
        }
    }

    impl Encode<String> for u64 {
        fn encode(&self) -> String {
            format!("{:016x}", *self)
        }
    }

    impl Encode<String> for i64 {
        fn encode(&self) -> String {
            format!("{:016x}", *self)
        }
    }


    impl Decode for u8 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_u8().unwrap()
        }
    }

    impl Decode for i8 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_i8().unwrap()
        }
    }

    impl Decode for u16 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_u16().unwrap()
        }
    }

    impl Decode for i16 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_i16().unwrap()
        }
    }

    impl Decode for u32 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_u32().unwrap()
        }
    }

    impl Decode for i32 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_i32().unwrap()
        }
    }

    impl Decode for u64 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_u64().unwrap()
        }
    }

    impl Decode for i64 {
        fn decode<U: ToParser>(inp: U) -> Self {
            let p = inp.to_parser();
            p.get_i64().unwrap()
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

    #[test]
    fn u8_encode_decode() {
        for (u, enc) in U8_CASES.iter() {
            assert_eq!(enc.to_owned(), u.encode());
            assert_eq!(u8::decode(enc.to_owned()), *u);
        }
    }

    const I8_CASES: [(i8, &'static str); 5] = [
        (0x00, "00"),
        (0x01, "01"),
        (0x7f, "7f"),
        (-128, "80"),
        (-1, "ff"),
    ];

    #[test]
    fn i8_encode_decode() {
        for (i, enc) in I8_CASES.iter() {
            assert_eq!(enc.to_owned(), i.encode());
            assert_eq!(i8::decode(enc.to_owned()), *i);
        }
    }

    const U16_CASES: [(u16, &'static str); 5] = [
        (0x0000, "0000"),
        (0x0001, "0001"),
        (0x7fff, "7fff"),
        (0x8000, "8000"),
        (0xffff, "ffff"),
    ];

    #[test]
    fn u16_encode_decode() {
        for (u, enc) in U16_CASES.iter() {
            assert_eq!(enc.to_owned(), u.encode());
            assert_eq!(u16::decode(enc.to_owned()), *u);
        }
    }

    const I16_CASES: [(i16, &'static str); 5] = [
        (0x0000, "0000"),
        (0x0001, "0001"),
        (0x7fff, "7fff"),
        (-0x8000, "8000"),
        (-0x1, "ffff"),
    ];

    #[test]
    fn i16_encode_decode() {
        for (i, enc) in I16_CASES.iter() {
            assert_eq!(enc.to_owned(), i.encode());
            assert_eq!(i16::decode(enc.to_owned()), *i);
        }
    }
}