//! Fixed-length analogues of variable-length types
//!
//! This module contains definitions of the primary fixed-width
//! schema types, [`FixedBytes<N>`] for opaque byte-sequences and
//! [`FixedString<N>`] for fixed-width strings.
//!
//! In both cases, the const generic `N` is the constant number of bytes
//! such values invariably hold.

use crate::conv::{ len, target::Target, Decode, Encode };
use crate::parse::{ ParseResult, Parser };
use std::borrow::Borrow;
use std::convert::{ TryInto, TryFrom };
use std::str::FromStr;
#[cfg(feature = "serde_impls")]
use serde::Serialize;

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


#[cfg(feature = "serde_impls")]
impl<const N: usize> Serialize for FixedBytes<N> where [u8; N]: Serialize {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
        self.0.serialize(serializer)
    }
}

impl<const N: usize> FixedBytes<N> {
    /// Constructs a [`FixedBytes<N>`] from a byte-array of length `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium::fixed::FixedBytes;
    /// assert_eq!(FixedBytes::from_array([1, 2, 3u8]).as_slice(), &[1, 2, 3u8]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn from_array(arr: [u8; N]) -> FixedBytes<N> {
        Self(arr)
    }

    /// Returns an immutable reference to the raw bytes of this [`FixedBytes<N>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium
    /// let arr : [u8; 4] = [0xde, 0xad, 0xbe, 0xef];
    /// assert_eq!(FixedBytes::from_array(&arr).bytes(), arr);
    /// ```
    #[inline]
    #[must_use]
    pub const fn bytes(&self) -> &[u8; N] {
        &self.0
    }

    /// Returns a mutable reference to the raw bytes of this [`FixedBytes<N>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tediumedBytes;
    /// let arr : [u8; 4] = [0xde, 0xad, 0xbe, 0xef];
    /// let mut data = FixedBytes::from_array(&arr);
    /// data.bytes_mut()[0] = 0xec;
    /// assert_eq!(data.bytes(), &[0xec, 0xad, 0xbe, 0xef]);
    /// ```
    #[inline]
    #[must_use]
    pub fn bytes_mut(&mut self) -> &mut [u8; N] {
        &mut self.0
    }

    /// Creates a new [`FixedBytes<N>`] by copying the contents of an referenced
    /// `N`-byte array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium::fixed::FixedBytes;
    /// let bytes : &'static [u8; 11] = b"hello world";
    /// assert_eq!(FixedBytes::from_slice(bytes).as_slice(), bytes);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn from_array_ref(arr: &'_ [u8; N]) -> FixedBytes<N> {
        Self(*arr)
    }


    /// Attempts to construct a [`FixedBytes<N>`] by copying the bytes of a
    /// byte-slice whose length is presumptively equal to `N`.
    ///
    /// # Errors
    ///
    /// Returns [`WidthError::WrongWidth`] if `bytes.len() != N`.
    pub const fn try_from_slice(bytes: &'_ [u8]) -> Result<FixedBytes<N>, crate::error::WidthError> {
        if bytes.len() == N {
            let ptr = bytes.as_ptr() as *const [u8; N];
            unsafe { Ok(Self(*ptr)) }
        } else {
            Err(crate::error::WidthError::WrongWidth { exact: N, actual: bytes.len() })
        }
    }


    /// Returns the length, in bytes, of this [FixedBytes<N>].
    ///
    /// # Note
    ///
    /// The return value will always be equal to `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium::fixed::FixedBytes;
    /// const LEN : usize = 42;
    /// assert_eq!(FixedBytes::from_array_ref(&[0u8; LEN]).len(), LEN);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn len(&self) -> usize {
        N
    }

    /// Returns the contents of this [`FixedBytes<N>`], as [`[u8; N]`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium::fixed::FixedBytes;
    /// let data : FixedBytes<4> = FixedBytes::from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    /// assert_eq!(data.to_array(), [0xde, 0xad, 0xbe, 0xef]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub const fn to_array(self) -> [u8; N] {
        self.0
    }

    /// Returns a freshly-allocated [Vec<u8>] holding the binary contents of this [FixedBytes<N>].
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> Vec<u8> {
        self.0.to_vec()
    }
}

impl<const N: usize> std::fmt::LowerHex for FixedBytes<N> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        crate::hexstring::util::write_hex! {
            fmt;
            &self.0
        }
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
        buf.push_many(self.0) + buf.resolve_zero()
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
    #[inline]
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
    #[must_use]
    /// Returns the length of this [`FixedString<N>`], measured in bytes.
    ///
    /// # Note
    ///
    /// The value returned by this function will always be equal to the generic constant `N`.
    pub const fn len(&self) -> usize {
        N
    }

    /// Constructs a [`FixedString<N>`] from a raw byte-array without UTF-8
    /// validation.
    ///
    /// # Safety
    ///
    /// Many associated methods and trait implementations over [`FixedString`]
    /// implicitly assume that the underlying bytes are valid UTF-8. As this
    /// method forgoes any checks that would prevent invalid instances from
    /// being constructed, it is unsafe in any context where the contents of the
    /// byte-array cannot be statically promised or guaranteed to be valid as
    /// UTF-8 data.
    ///
    /// If such guarantees are not possible, [try_from_array] should be used instead.
    #[must_use]
    #[inline(always)]
    pub const unsafe fn from_array_unchecked(arr: &[u8; N]) -> Self {
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
    /// # use ::tedium::fixed::FixedString;
    ///
    /// const MOGAMI_STR : &'static str = "さみだれをあつめてはやしもがみがわ";
    /// const MOGAMI_ARR : &[u8; 51] = b"\xE3\x81\x95\xE3\x81\xBF\xE3\x81\xA0\xE3\x82\x8C\xE3\x82\x92\xE3\x81\x82\xE3\x81\xA4\xE3\x82\x81\xE3\x81\xA6\xE3\x81\xAF\xE3\x82\x84\xE3\x81\x97\xE3\x82\x82\xE3\x81\x8C\xE3\x81\xBF\xE3\x81\x8C\xE3\x82\x8F";
    ///
    ///
    /// let haiku : FixedString<51> = FixedString::try_from_array(MOGAMI_ARR).unwrap();
    /// assert_eq!(haiku.as_str(), MOGAMI_STR);
    /// ```
    #[inline]
    pub const fn try_from_array(arr: &[u8; N]) -> Result<Self, std::str::Utf8Error> {
        match std::str::from_utf8(arr) {
            Ok(_) => Ok(Self { contents: *arr }),
            Err(e) => Err(e),
        }
    }

    /// Returns `true` if this [`FixedString`] is valid as UTF-8, and can therefore be
    /// converted to strings without issue.
    ///
    /// # Examples
    ///
    /// ```
    /// # use tedium::fixed::FixedString;
    /// let valid : FixedString::<4> = FixedString::from_str("🦀");
    /// assert_eq!(valid.is_valid_utf8());
    /// let invalid : FixedString::<1> = FixedString::from_array_unchecked([0x00]);
    /// assert!(!invalid.is_valid_utf8());
    /// ```
    pub const fn is_valid_utf8(&self) -> bool {
        matches!(std::str::from_utf8(&self.contents), Ok(_))
    }

    /// Returns a string representation of the binary contents of this [`FixedString`] object.
    ///
    /// # Safety
    ///
    /// This method performs an unchecked UTF-8 conversion from `&[u8]` to `&str`,
    /// which is inherently unsafe. It should only be used on data that is known
    /// in advance to be valid UTF-8, either by construction or by guarding with
    /// the predicate function [`is_valid_utf8`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::tedium::fixed::FixedString;
    /// let text : &'static str = "hello world";
    /// assert_eq!(unsafe { FixedString::from_str(text).as_str_unchecked() }, str);
    /// ```
    pub unsafe fn as_str_unchecked(&self) -> &str {
        std::str::from_utf8_unchecked(&self.contents)
    }

    /// Converts a [`FixedString`] to a string, including invalid characters.
    ///
    /// (Cf. `String::from_utf8_lossy`)
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::tedium::fixed::FixedString;
    /// let arr : [u8; 4] = [0x00, 0x61, 0xec, 0xad]
    /// let data : FixedString<4> = FixedString::from_array_unchecked(arr);
    /// assert_eq!(data.as_string_lossy(), Cow::Owned(String::from("\x00a�"))
    /// ```
    pub fn as_string_lossy(&self) -> std::borrow::Cow<'_, str> {
        String::from_utf8_lossy(&self.contents)
    }

    /// Attempt to convert a slice of possibly incorrect length into a [`FixedString<N>`].
    ///
    /// # Note
    ///
    /// The class of error returned by this method only reports failure occuring when
    /// the length of the slice is incorrect for the generic length argument of the output
    /// type (the `N` in [`FixedString<N>`]). Specifically, it will return 'success' for
    /// conversions of byte-slices that do not represent valid UTF-8. As a result, it is
    /// strongly recommended that [`is_valid_utf8`] be used to guard against such unreported
    /// invalidities before using the return value any further.
    ///
    /// # Errors
    ///
    /// Will return [`WrongWidth`](crate::error::WidthError::WrongWidth) if
    /// `bytes.len() != N`.
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