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

    fn encode_decode<U, const N: usize>(table: [(U, &'static str); N])
    where
        U: Encode<String> + Decode + std::cmp::PartialEq + std::fmt::Debug,
    {
        for (u, enc) in table.iter() {
            assert_eq!(enc.to_owned(), u.encode());
            assert_eq!(U::decode(enc.to_owned()), *u);
        }
    }

    const U8_CASES: [(u8, &'static str); 5] = [
        (0x00, "00"),
        (0x01, "01"),
        (0x7f, "7f"),
        (0x80, "80"),
        (0xff, "ff"),
    ];

    #[test]
    fn u8_encode_decode() {
        encode_decode(U8_CASES)
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
        encode_decode(I8_CASES)
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
        encode_decode(U16_CASES)
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
        encode_decode(I16_CASES)
    }

    const U32_CASES: [(u32, &'static str); 5] = [
        (0x0000_0000, "00000000"),
        (0x0000_0001, "00000001"),
        (0x7fff_ffff, "7fffffff"),
        (0x8000_0000, "80000000"),
        (0xffff_ffff, "ffffffff"),
    ];

    #[test]
    fn u32_encode_decode() {
        encode_decode(U32_CASES)
    }

    const I32_CASES: [(i32, &'static str); 5] = [
        (0x0000_0000, "00000000"),
        (0x0000_0001, "00000001"),
        (0x7fff_ffff, "7fffffff"),
        (-0x8000_0000, "80000000"),
        (-0x1, "ffffffff"),
    ];

    #[test]
    fn i32_encode_decode() {
        encode_decode(I32_CASES)
    }

    const U64_CASES: [(u64, &'static str); 5] = [
        (0x0000000000000000, "0000000000000000"),
        (0x0000000000000001, "0000000000000001"),
        (0x7fffffffffffffff, "7fffffffffffffff"),
        (0x8000000000000000, "8000000000000000"),
        (0xffffffffffffffff, "ffffffffffffffff"),
    ];

    #[test]
    fn u64_encode_decode() {
        encode_decode(U64_CASES)
    }

    const I64_CASES: [(i64, &'static str); 5] = [
        (0x0000000000000000, "0000000000000000"),
        (0x0000000000000001, "0000000000000001"),
        (0x7fffffffffffffff, "7fffffffffffffff"),
        (-0x8000000000000000, "8000000000000000"),
        (-0x1, "ffffffffffffffff"),
    ];

    #[test]
    fn i64_encode_decode() {
        encode_decode(I64_CASES)
    }

}
