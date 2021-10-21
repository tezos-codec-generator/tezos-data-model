use crate::conv::{Decode, Encode};
use crate::parse::byteparser::ToParser;
use crate::builder;

impl Encode for bool {
    fn encode<U: builder::Builder>(&self) -> U {
        match self {
            &true => U::word(0xff),
            &false => U::word(0x00),
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
        use crate::builder::{Builder};

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        pub struct ByteString<const N: usize>([u8; N]);

        impl<const N: usize> From<&[u8; N]> for ByteString<N> {
            fn from(arr: &[u8; N]) -> Self {
                Self(arr.clone())
            }
        }

        impl<const N: usize> Encode for ByteString<N> {
            fn encode<U: Builder>(&self) -> U {
                U::words(self.0)
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
            use crate::{builder::owned::OwnedBuilder, hex};
            use super::*;
            use crate::parse::hexstring::HexString;

            #[test]
            fn bytestring_hex() {
                let hex = hex!("deadbeef");
                let b = ByteString::<4>::decode(hex);
                assert_eq!(b, ByteString([0xde,0xad,0xbe,0xef]));
                assert_eq!(b.encode::<OwnedBuilder>().show_hex(), "deadbeef");
            }
            
            #[test]
            fn bytestring_ascii() {
                let b = ByteString::<12>::decode("hello world!");
                assert_eq!(b, ByteString::from(b"hello world!"));
                assert_eq!(b.encode::<OwnedBuilder>().show().unwrap(), "hello world!");
            }

        }
    }

    pub mod charstring {
        use std::convert::TryInto;

        use crate::builder::Builder;
        use crate::conv::{Decode, Encode};
        use crate::parse::{byteparser::ToParser};

        #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
        pub struct CharString<const N: usize> {
            contents: [u8; N]
        }

        impl<const N: usize> From<&str> for CharString<N> {
            fn from(x: &str) -> Self {
                let n = x.len();
                if N != n {
                    panic!("Cannot convert {}-byte string into CharString<{}>: `{}`", n, N, x);
                }
                Self { contents: x.as_bytes().try_into().unwrap() }
           }
        }

        impl<const N: usize> From<[u8; N]> for CharString<N> {
            fn from(arr: [u8; N]) -> Self {
                Self { contents: arr }
            }
        }

        impl<const N: usize> From<&[u8; N]> for CharString<N> {
            fn from(arr: &[u8; N]) -> Self {
                Self { contents: arr.to_owned() }
            }
        }

        impl<const N: usize> Encode for CharString<N> {
            fn encode<U: Builder>(&self) -> U {
                U::words(self.contents)
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
            use crate::builder::owned::OwnedBuilder;
            use std::borrow::Borrow;

            use super::*;

            fn check_str<const N: usize>(case: &'static str) {
                let res = CharString::<N>::decode(case);
                assert_eq!(res, CharString::from(case));
                assert_eq!(res.encode::<OwnedBuilder>().show().unwrap(), case);
            }

            fn check_arr<const N: usize>(case: &[u8; N]) {
                let res = CharString::<N>::decode(case);
                assert_eq!(res, CharString::from(case));
                assert_eq!(<OwnedBuilder as Borrow<[u8]>>::borrow(&res.encode::<OwnedBuilder>()), case);
            }


            #[test]
            fn charstring() {
                check_arr::<12>(b"hello world!");
                check_str::<12>("さよなら");
            }
        }
    }
}