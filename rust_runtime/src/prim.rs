use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;

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

pub mod fixed {
    pub mod bytestring {
        use crate::conv::{Decode, Encode};
        use crate::parse::byteparser::ToParser;

        struct ByteString<const N: usize>([u8; N]);

        impl<const N: usize> Encode<String> for ByteString<N> {
            fn encode(&self) -> String {
                format!("{:02x?}", self.0) 
            }
        }

        impl<const N: usize> Decode for ByteString<N> {
            fn decode<U: ToParser>(inp: U) -> Self {
                let p = inp.to_parser();
                ByteString(p.get_fixed::<N>().unwrap())
            }
        }
    }

    pub mod charstring {
        use crate::conv::{Decode, Encode};
        use crate::parse::byteparser::ToParser;

        struct CharString<const N: usize>([u8; N]);

        impl<const N: usize> Encode<String> for CharString<N> {
            fn encode(&self) -> String {
                unsafe { String::from_utf8_unchecked(self.0.to_vec()) }
            }
        }

        impl<const N: usize> Decode for CharString<N> {
            fn decode<U: ToParser>(inp: U) -> Self {
                let p = inp.to_parser();
                CharString(p.get_fixed::<N>().unwrap())
            }
        }

    }
}