use crate::conv::{Decode, Encode};
use crate::parse::byteparser::{ToParser};

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
