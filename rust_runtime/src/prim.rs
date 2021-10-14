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

impl Encode<Vec<u8>> for bool {
    fn encode(&self) -> Vec<u8> {
        match self {
            &true => Vec::from([0xff]),
            &false => Vec::from([0x00]),
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

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        struct ByteString<const N: usize>([u8; N]);

        impl<const N: usize> Encode<String> for ByteString<N> {
            fn encode(&self) -> String {
                self.0.iter().map(u8::encode).collect::<String>()
            }
        }

        impl<const N: usize> Decode for ByteString<N> {
            fn decode<U: ToParser>(inp: U) -> Self {
                let p = inp.to_parser();
                ByteString(p.get_fixed::<N>().unwrap())
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;
            #[test]
            fn bytestring() {
                let b = ByteString::<4>::decode("deadbeef");
                assert_eq!(b, ByteString([0xde,0xad,0xbe,0xef]));
                assert_eq!(b.encode(), "deadbeef");
            }
        }
    }

    pub mod charstring {
        use crate::conv::{Decode, Encode};
        use crate::parse::byteparser::ToParser;

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        struct CharString<const N: usize> {
            contents: String
        }

        impl<const N: usize> From<&str> for CharString<N> {
            fn from(s: &str) -> Self {
                assert_eq!(s.len(), N);
                Self { contents: s.to_owned() }
            }
        }

        impl<const N: usize> From<String> for CharString<N> {
            fn from(s: String) -> Self {
                assert_eq!(s.len(), N);
                Self { contents: s }
            }
        }

        impl<const N: usize> From<[u8; N]> for CharString<N> {
            fn from(arr: [u8; N]) -> Self {
                Self { contents: String::from_utf8_lossy(&arr).into_owned()}
            }
        }

        impl<const N: usize> Encode<String> for CharString<N> {
            fn encode(&self) -> String {
                self.contents.clone()
            }
        }

        impl<const N: usize> Decode for CharString<N> {
            fn decode<U: ToParser>(inp: U) -> Self {
                let p = inp.to_parser();
                p.get_fixed::<N>().unwrap().into()
            }
        }
        #[cfg(test)]
        mod tests {
            use super::*;
            #[test]
            fn charstring() {
                let b = CharString::<12>::decode(b"hello world!");
                assert_eq!(b, CharString::from("hello world!"));
                assert_eq!(b.encode(), "hello world!");
            }
        }
    }
}