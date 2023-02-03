//! Fixed-length analogues of variable-length types
//!
//! This module contains definitions of the primary fixed-width
//! schema types, [`FixedBytes<N>`] for opaque byte-sequences and
//! [`FixedString<N>`] for fixed-width strings.
//!
//! In both cases, the const generic `N` is the number of bytes
//! such a value is required to contain.

use crate::conv::{ len, target::Target, Decode, Encode };
use crate::parse::{ ParseResult, Parser };
use std::borrow::Borrow;
use std::convert::{ TryInto, TryFrom };
use std::str::FromStr;

/// Simple type for holding fixed-length binary sequences.
///
/// While [FixedBytes<N>] is naturally implemented around `[u8; N]`,
/// it is preferable to use this type instead, in order to signal to
/// downstream consumers that the data in question is specifically
/// intended to be interpreted as raw binary data, and not as an unboxed
/// UTF-8 string (as with [FixedString<N>]).
///
/// Many intuitive conversion traits are implemented to allow flexible
/// construction and reinterpretation of `FixedBytes` values, with
/// comparably little overhead versus using arrays directly.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct FixedBytes<const N: usize>([u8; N]);

impl<const N: usize> FixedBytes<N> {
    /// Returns the (constant) length of a [FixedBytes<N>] in bytes,
    /// namely `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::fixed::FixedBytes;
    /// assert_eq!(FixedBytes::<5>::from(&[1,2,3,4,5u8]), 5);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn len(&self) -> usize {
        N
    }

    /// Returns a constant slice reference to the contents of a borrowed
    /// [FixedBytes<N>]
    #[inline(always)]
    #[must_use]
    pub const fn as_slice(&self) -> &[u8; N] {
        &self.0
    }

    /// Returns a freshly-allocated [Vec<u8>] holding the same contents as
    /// a borrowed [FixedBytes<N>].
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }
}


impl<const N: usize> AsRef<[u8; N]> for FixedBytes<N> {
    fn as_ref(&self) -> &[u8; N] {
        &self.0
    }
}

impl<const N: usize> AsRef<[u8]> for FixedBytes<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> Borrow<[u8; N]> for FixedBytes<N> {
    fn borrow(&self) -> &[u8; N] {
        &self.0
    }
}

impl<const N: usize> Borrow<[u8]> for FixedBytes<N> {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> From<FixedBytes<N>> for Vec<u8> {
    fn from(bytes: FixedBytes<N>) -> Self {
        bytes.0.into()
    }
}

impl<const N: usize> From<FixedBytes<N>> for [u8; N] {
    fn from(bytes: FixedBytes<N>) -> Self {
        bytes.0
    }
}

impl<const N: usize> Default for FixedBytes<N> where [u8; N]: Default {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<const N: usize> From<&[u8; N]> for FixedBytes<N> {
    fn from(arr: &[u8; N]) -> Self {
        Self(*arr)
    }
}

impl<const N: usize> From<[u8; N]> for FixedBytes<N> {
    fn from(value: [u8; N]) -> Self {
        Self(value)
    }
}

impl<'a, const N: usize> TryFrom<&'a [u8]> for FixedBytes<N> {
    type Error = <[u8; N] as TryFrom<&'a [u8]>>::Error;

    fn try_from(value: &'a [u8]) -> Result<Self, Self::Error> {
        Ok(Self(value.try_into()?))
    }
}

impl<const N: usize> len::FixedLength for FixedBytes<N> {
    const LEN: usize = N;
}

impl<const N: usize> Encode for FixedBytes<N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(&self.0) + buf.resolve_zero()
    }

    #[inline]
    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(&self.0)
    }

    fn encode<U: Target>(&self) -> U {
        let mut buf: U = U::create();
        let _ = self.write_to::<U>(&mut buf);
        buf
    }

    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        self.0.to_vec()
    }
}

impl<const N: usize> Decode for FixedBytes<N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(Self(p.take_fixed::<N>()?))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FixedString<const N: usize> {
    contents: [u8; N],
}

impl<const N: usize> FixedString<N> {
    #[inline]
    pub const fn len(&self) -> usize {
        N
    }

    ///
    pub unsafe fn from_array_unchecked(arr: &[u8; N]) -> Self {
        Self { contents: *arr }
    }

    /// Attempt to construct a `FixedString<N>` from a borrowed byte-array of length `N`.
    ///
    /// Will return [`Utf8Error`](std::str::Utf8Error) if `arr` does not encode to valid UTF-8,
    /// as determined by the return value of [`std::str::from_utf8`]
    ///
    /// # Example
    ///
    /// ```
    /// # use ::rust_runtime::fixed::FixedString;
    ///
    /// const MOGAMI_STR : &'static str = "さみだれをあつめてはやしもがみがわ";
    /// const MOGAMI_ARR : &[u8; 51] = b"\xE3\x81\x95\xE3\x81\xBF\xE3\x81\xA0\xE3\x82\x8C\xE3\x82\x92\xE3\x81\x82\xE3\x81\xA4\xE3\x82\x81\xE3\x81\xA6\xE3\x81\xAF\xE3\x82\x84\xE3\x81\x97\xE3\x82\x82\xE3\x81\x8C\xE3\x81\xBF\xE3\x81\x8C\xE3\x82\x8F";
    ///
    ///
    /// let haiku : FixedString<51> = FixedString::try_from_array(MOGAMI_ARR).unwrap();
    /// assert_eq!(haiku.as_str(), MOGAMI_STR);
    /// ```
    ///
    ///
    pub fn try_from_array(arr: &[u8; N]) -> Result<Self, std::str::Utf8Error> {
        let _ = std::str::from_utf8(arr)?;
        Ok(Self { contents: *arr })
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.contents) }
    }

    pub fn as_string(&self) -> std::borrow::Cow<'_, str> {
        String::from_utf8_lossy(&self.contents)
    }

    /// Attempt to convert a slice of possibly incorrect length into a `FixedString<N>`
    ///
    /// # Errors
    ///
    /// Will return [`WrongWidth`](crate::error::WidthError::WrongWidth) if
    /// `bytes.len() != N`
    #[inline]
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, crate::error::WidthError> {
        if let Ok(contents) = bytes.try_into() {
            Ok(Self { contents })
        } else {
            Err(crate::error::WidthError::WrongWidth {
                exact: N,
                actual: bytes.len(),
            })
        }
    }
}

impl<const N: usize> len::FixedLength for FixedString<N> {
    const LEN: usize = N;
}

impl<const N: usize> FromStr for FixedString<N> {
    type Err = crate::error::WidthError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from_bytes(s.as_bytes())
    }
}

impl<const N: usize> TryFrom<String> for FixedString<N> {
    type Error = crate::error::WidthError;

    #[inline]
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::try_from_bytes(s.as_bytes())
    }
}

impl<const N: usize> TryFrom<&str> for FixedString<N> {
    type Error = crate::error::WidthError;

    #[inline]
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::try_from_bytes(s.as_bytes())
    }
}

impl<const N: usize> TryFrom<&[u8]> for FixedString<N> {
    type Error = crate::error::WidthError;

    fn try_from(bytes: &[u8]) -> Result<Self, Self::Error> {
        Self::try_from_bytes(bytes)
    }
}

impl<const N: usize> From<[u8; N]> for FixedString<N> {
    #[inline]
    fn from(contents: [u8; N]) -> Self {
        Self { contents }
    }
}

impl<const N: usize> From<&[u8; N]> for FixedString<N> {
    #[inline]
    fn from(arr: &[u8; N]) -> Self {
        Self { contents: *arr }
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

impl<const N: usize> std::fmt::Display for FixedString<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        String::from_utf8_lossy(&self.contents).fmt(f)
    }
}

#[cfg(test)]
mod fixedstring_tests {
    use crate::{ Builder, StrictBuilder };
    use std::{ borrow::Borrow, convert::TryFrom };

    use super::*;

    fn check_str<const N: usize>(case: &'static str) {
        let res = if cfg!(feature = "implicit_hexstring") {
            FixedString::<N>::decode(case.as_bytes())
        } else {
            FixedString::<N>::decode(case)
        };
        assert_eq!(res, FixedString::try_from(case).unwrap());
        assert_eq!(res.encode::<StrictBuilder>().into_bin().unwrap(), case);
        assert_eq!(res.to_string(), case);
    }

    fn check_arr<const N: usize>(case: &[u8; N]) {
        let res = FixedString::<N>::decode(case);
        assert_eq!(res, FixedString::from(case));
        assert_eq!(<StrictBuilder as Borrow<[u8]>>::borrow(&res.encode::<StrictBuilder>()), case);
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
    use crate::{ builder::{ strict::StrictBuilder, Builder }, hex };

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
        assert_eq!(b.encode::<StrictBuilder>().into_bin().unwrap(), "hello world!");
    }
}