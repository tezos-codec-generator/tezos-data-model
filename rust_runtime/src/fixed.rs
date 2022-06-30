//! Fixed-length analogues of variable-length types
//!
//! This module contains definitions of the primary fixed-width
//! schema types, [`FixedBytes<N>`] for opaque byte-sequences and
//! [`FixedString<N>`] for fixed-width strings.
//!
//! In both cases, the const generic `N` is the number of bytes
//! such a value is required to contain.

use crate::conv::{len, target::Target, Decode, Encode};
use crate::parse::{ParseResult, Parser};
use std::convert::TryInto;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub struct FixedBytes<const N: usize>([u8; N]);

impl<const N: usize> Default for FixedBytes<N>
where
    [u8; N]: Default,
{
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<const N: usize> From<&[u8; N]> for FixedBytes<N> {
    fn from(arr: &[u8; N]) -> Self {
        Self(*arr)
    }
}

impl<const N: usize> len::FixedLength for FixedBytes<N> {
    const LEN: usize = N;
}

impl<const N: usize> Encode for FixedBytes<N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(&self.0) + buf.resolve_zero()
    }
}

impl<const N: usize> Decode for FixedBytes<N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(FixedBytes(p.take_fixed::<N>()?))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy, Hash)]
pub struct FixedString<const N: usize> {
    contents: [u8; N],
}

impl<const N: usize> Default for FixedString<N>
where
    [u8; N]: Default,
{
    fn default() -> Self {
        Self {
            contents: Default::default(),
        }
    }
}

impl<const N: usize> len::FixedLength for FixedString<N> {
    const LEN: usize = N;
}

impl<const N: usize> std::convert::TryFrom<&str> for FixedString<N> {
    type Error = crate::error::WidthError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let n: usize = value.len();
        if N != n {
            Err(crate::error::WidthError::WrongWidth {
                exact: N,
                actual: n,
            })
        } else {
            Ok(Self {
                contents: value.as_bytes().try_into().unwrap(),
            })
        }
    }
}

impl<const N: usize> From<[u8; N]> for FixedString<N> {
    fn from(arr: [u8; N]) -> Self {
        Self { contents: arr }
    }
}

impl<const N: usize> From<&[u8; N]> for FixedString<N> {
    fn from(arr: &[u8; N]) -> Self {
        Self {
            contents: arr.to_owned(),
        }
    }
}

impl<const N: usize> Encode for FixedString<N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(&self.contents) + buf.resolve_zero()
    }
}

impl<const N: usize> Decode for FixedString<N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(p.take_fixed::<N>()?.into())
    }
}
#[cfg(test)]
mod fixedstring_tests {
    use crate::{Builder, StrictBuilder};
    use std::{borrow::Borrow, convert::TryFrom};

    use super::*;

    fn check_str<const N: usize>(case: &'static str) {
        let res = if cfg!(feature = "implicit_hexstring") {
            FixedString::<N>::decode(case.as_bytes())
        } else {
            FixedString::<N>::decode(case)
        };
        assert_eq!(res, FixedString::try_from(case).unwrap());
        assert_eq!(res.encode::<StrictBuilder>().into_bin().unwrap(), case);
    }

    fn check_arr<const N: usize>(case: &[u8; N]) {
        let res = FixedString::<N>::decode(case);
        assert_eq!(res, FixedString::from(case));
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

#[cfg(test)]
mod fixedbytes_tests {
    use super::*;
    use crate::{
        builder::{strict::StrictBuilder, Builder},
        hex,
    };

    #[test]
    fn bytestring_hex() {
        let hex = hex!("deadbeef");
        let b = FixedBytes::<4>::decode(hex);
        assert_eq!(b, FixedBytes([0xde, 0xad, 0xbe, 0xef]));
        assert_eq!(b.encode::<StrictBuilder>().into_hex(), "deadbeef");
    }

    #[test]
    fn bytestring_ascii() {
        let b = FixedBytes::<12>::decode(b"hello world!");
        assert_eq!(b, FixedBytes::from(b"hello world!"));
        assert_eq!(
            b.encode::<StrictBuilder>().into_bin().unwrap(),
            "hello world!"
        );
    }
}
