#[derive(Clone, Copy, Debug)]
pub struct LengthMismatchError {
    expected: usize,
    actual: usize,
}

impl std::fmt::Display for LengthMismatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}-byte value cannot be coerced into fixed {}-byte type",
            &self.actual, &self.expected
        )
    }
}

impl LengthMismatchError {
    pub(crate) fn new(expected: usize, actual: usize) -> Self {
        Self { expected, actual }
    }
}

pub mod bytestring {
    use crate::conv::{len, Decode, Encode};
    use crate::parse::byteparser::ParseResult;
    use crate::parse::byteparser::Parser;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
    pub struct ByteString<const N: usize>([u8; N]);

    impl<const N: usize> From<&[u8; N]> for ByteString<N> {
        fn from(arr: &[u8; N]) -> Self {
            Self(arr.clone())
        }
    }

    impl<const N: usize> len::FixedLength for ByteString<N> {
        const LEN: usize = N;
    }

    impl<const N: usize> Encode for ByteString<N> {
        fn write(&self, buf: &mut Vec<u8>) {
            buf.extend(self.0)
        }
    }

    impl<const N: usize> Decode for ByteString<N> {
        fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
            Ok(ByteString(p.get_fixed::<N>()?))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::{
            builder::{owned::OwnedBuilder, Builder},
            hex,
        };

        #[test]
        fn bytestring_hex() {
            let hex = hex!("deadbeef");
            let b = ByteString::<4>::decode(hex);
            assert_eq!(b, ByteString([0xde, 0xad, 0xbe, 0xef]));
            assert_eq!(b.encode::<OwnedBuilder>().into_hex(), "deadbeef");
        }

        #[test]
        fn bytestring_ascii() {
            let b = ByteString::<12>::decode(b"hello world!");
            assert_eq!(b, ByteString::from(b"hello world!"));
            assert_eq!(
                b.encode::<OwnedBuilder>().into_bin().unwrap(),
                "hello world!"
            );
        }
    }
}

pub mod charstring {
    use std::convert::TryInto;

    use crate::conv::{len, Decode, Encode};
    use crate::parse::byteparser::{ParseResult, Parser};

    use super::LengthMismatchError;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy)]
    pub struct CharString<const N: usize> {
        contents: [u8; N],
    }

    impl<const N: usize> len::FixedLength for CharString<N> {
        const LEN: usize = N;
    }

    impl<const N: usize> std::convert::TryFrom<&str> for CharString<N> {
        type Error = LengthMismatchError;

        fn try_from(value: &str) -> Result<Self, Self::Error> {
            let n: usize = value.len();
            if N != n {
                Err(LengthMismatchError::new(N, n))
            } else {
                Ok(Self {
                    contents: value.as_bytes().try_into().unwrap(),
                })
            }
        }
    }

    impl<const N: usize> From<[u8; N]> for CharString<N> {
        fn from(arr: [u8; N]) -> Self {
            Self { contents: arr }
        }
    }

    impl<const N: usize> From<&[u8; N]> for CharString<N> {
        fn from(arr: &[u8; N]) -> Self {
            Self {
                contents: arr.to_owned(),
            }
        }
    }

    impl<const N: usize> Encode for CharString<N> {
        fn write(&self, buf: &mut Vec<u8>) {
            buf.extend(self.contents)
        }
    }

    impl<const N: usize> Decode for CharString<N> {
        fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
            Ok(p.get_fixed::<N>()?.into())
        }
    }
    #[cfg(test)]
    mod tests {
        use crate::{builder::owned::OwnedBuilder, Builder, StrictBuilder};
        use std::{borrow::Borrow, convert::TryFrom};

        use super::*;

        fn check_str<const N: usize>(case: &'static str) {
            let res = CharString::<N>::decode(case);
            assert_eq!(res, CharString::try_from(case).unwrap());
            assert_eq!(res.encode::<OwnedBuilder>().into_bin().unwrap(), case);
        }

        fn check_arr<const N: usize>(case: &[u8; N]) {
            let res = CharString::<N>::decode(case);
            assert_eq!(res, CharString::from(case));
            assert_eq!(
                <StrictBuilder as Borrow<[u8]>>::borrow(&res.encode::<StrictBuilder>()),
                case
            );
        }

        #[test]
        fn charstring() {
            check_arr::<12>(b"hello world!");
            check_str::<12>("さよなら");
        }
    }
}
