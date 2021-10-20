use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;

impl Encode<Vec<u8>> for bool {
    fn encode(&self) -> Vec<u8> {
        match self {
            &true => Vec::from([0xff]),
            &false => Vec::from([0x00]),
        }
    }
}

impl Decode for bool {
    fn decode(inp: impl ToParser) -> Self {
        let p = inp.to_parser();
        p.get_bool().unwrap()
    }
}

pub mod fixed {
    pub mod bytestring {
        use crate::conv::{Decode, Encode};
        use crate::parse::byteparser::ToParser;

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        pub struct ByteString<const N: usize>([u8; N]);

        impl<const N: usize> From<&[u8; N]> for ByteString<N> {
            fn from(arr: &[u8; N]) -> Self {
                Self(arr.clone())
            }
        }

        impl<const N: usize> Encode<Vec<u8>> for ByteString<N> {
            fn encode(&self) -> Vec<u8> {
                self.0.to_vec()
            }
        }

        impl<const N: usize> Decode for ByteString<N> {
            fn decode(inp: impl ToParser) -> Self {
                let p = inp.to_parser();
                ByteString(p.get_fixed::<N>().unwrap())
            }
        }

        #[cfg(test)]
        mod tests {
            use crate::hex;
            use super::*;
            use crate::parse::hexstring::HexString;

            #[test]
            fn bytestring_hex() {
                let hex = hex!("deadbeef");
                let b = ByteString::<4>::decode(hex);
                assert_eq!(b, ByteString([0xde,0xad,0xbe,0xef]));
                assert_eq!(Encode::<HexString>::encode(&b).to_string(), "deadbeef");
            }
            
            #[test]
            fn bytestring_ascii() {
                let b = ByteString::<12>::decode("hello world!");
                assert_eq!(b, ByteString::from(b"hello world!"));
                assert_eq!(Encode::<String>::encode(&b), "hello world!");
            }

        }
    }

    pub mod charstring {
        use crate::conv::{Decode, Encode};
        use crate::parse::{byteparser::ToParser, hexstring::HexString};

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        pub struct CharString<const N: usize> {
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

        impl<const N: usize> Encode<HexString> for CharString<N> {
            fn encode(&self) -> HexString {
                HexString::from(self.contents.as_bytes())
            }
        }

        impl<const N: usize> Decode for CharString<N> {
            fn decode(inp: impl ToParser) -> Self {
                let p = inp.to_parser();
                p.get_fixed::<N>().unwrap().into()
            }
        }
        #[cfg(test)]
        mod tests {
            use super::*;

            fn check<const N: usize>(case: &'static str) {
                let res = CharString::<N>::decode(case);
                assert_eq!(res, CharString::from(case));
                assert_eq!(Encode::<String>::encode(&res), case);
            }

            #[test]
            fn charstring() {
                check::<12>("hello world!");
                check::<12>("さよなら");
            }
        }
    }
}