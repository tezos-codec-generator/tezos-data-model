pub mod bytestring {
    use crate::conv::{Decode, Encode, len};
    use crate::Parser;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
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
        fn parse<P: Parser>(p: &mut P) -> Self {
            ByteString(p.get_fixed::<N>().unwrap())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::{builder::{Builder, owned::OwnedBuilder}, hex};

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
            assert_eq!(b.encode::<OwnedBuilder>().into_bin().unwrap(), "hello world!");
        }
    }
}

pub mod charstring {
    use std::convert::TryInto;

    use crate::conv::{Decode, Encode, len};
    use crate::parse::byteparser::Parser;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
    pub struct CharString<const N: usize> {
        contents: [u8; N],
    }

    impl<const N: usize> len::FixedLength for CharString<N> {
        const LEN: usize = N;
    }

    impl<const N: usize> From<&str> for CharString<N> {
        fn from(x: &str) -> Self {
            let n = x.len();
            if N != n {
                panic!(
                    "Cannot convert {}-byte string into CharString<{}>: `{}`",
                    n, N, x
                );
            }
            Self {
                contents: x.as_bytes().try_into().unwrap(),
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
        fn parse<P: Parser>(p: &mut P) -> Self {
            p.get_fixed::<N>().unwrap().into()
        }
    }
    #[cfg(test)]
    mod tests {
        use crate::{Builder, builder::owned::OwnedBuilder};
        use std::borrow::Borrow;

        use super::*;

        fn check_str<const N: usize>(case: &'static str) {
            let res = CharString::<N>::decode(case);
            assert_eq!(res, CharString::from(case));
            assert_eq!(res.encode::<OwnedBuilder>().into_bin().unwrap(), case);
        }

        fn check_arr<const N: usize>(case: &[u8; N]) {
            let res = CharString::<N>::decode(case);
            assert_eq!(res, CharString::from(case));
            assert_eq!(
                <OwnedBuilder as Borrow<[u8]>>::borrow(&res.encode::<OwnedBuilder>()),
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
