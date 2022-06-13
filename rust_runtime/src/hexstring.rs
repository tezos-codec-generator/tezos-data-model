//! Validated conversion to and from hex-encoded strings
//!
//! This module defines the `HexString` struct, which is used for ensuring that
//! ambiguous string types are explicitly interpreted as being hex-strings, rather
//! than as one-to-one byte-sequences.
//!
//! This is also the module that defines the [`hex`] macro, which converts
//! from string-like types into `HexString` values.

use crate::error::ConvError::{self, HexError, ParityError};
use crate::{conv::target::Target, util::hex_of_bytes};
use std::{convert::TryFrom, iter::FromIterator};

pub use std::vec::IntoIter;

/// Newtype representing byte-arrays that are parsed from and displayed as
/// hexadecimally encoded `String` values, but stored in memory as byte-buffers
/// representing the individual words parsed from the string.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
#[repr(transparent)]
pub struct HexString {
    bytes: Vec<u8>,
}

impl HexString {
    /// Constructs a new, empty `HexString`
    ///
    /// Until it is written to, the underlying vector will remain unallocated.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self { bytes: Vec::new() }
    }

    /// Constructs a new `HexString` whose underlying vector
    /// is simply `<T as Into<Vec<u8>>>::into` applied to the
    /// provided argument.
    #[must_use]
    pub fn from_bytes<T: Into<Vec<u8>>>(bytes: T) -> Self {
        Self {
            bytes: bytes.into(),
        }
    }

    /// Destructs a `HexString` into its underlying byte-vector
    #[inline]
    #[must_use]
    pub fn into_vec(self) -> Vec<u8> {
        self.bytes
    }

    /// Extracts a slice containing the entirety of the underlying vector
    ///
    /// Equivalent to `self.as_vec().as_slice()`
    #[inline(always)]
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    /// Extracts a mutable slice containing the entirety of the underlying
    /// vector.
    ///
    /// Equivalent to `self.as_mut_vec().as_mut_slice()`
    #[inline(always)]
    #[must_use]
    pub fn as_mut_bytes(&mut self) -> &mut [u8] {
        self.bytes.as_mut_slice()
    }

    /// Extracts a reference to the underlying vector
    pub const fn as_vec(&self) -> &Vec<u8> {
        &self.bytes
    }

    /// Extracts a mutable reference to the underlying vector
    pub fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }

    /// Returns the number of bytes in the `HexString`
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns `true` if the `HexString` has length 0
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns a String consisting of a hexadecimal encoding of `self`,
    /// with two characters encoding each byte in order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::rust_runtime::{hex, HexString};
    /// assert_eq!(HexString::new().to_hex(), "");
    /// assert_eq!(HexString::from(vec![0xde, 0xad, 0xbe, 0xef]).to_hex(),"deadbeef");
    /// ```
    ///
    #[inline(always)]
    #[must_use]
    pub fn to_hex(&self) -> String {
        hex_of_bytes(&self.bytes)
    }
}

impl HexString {
    /// Attempt to parse a hexadecimally encoded string into the sequence of
    /// bytes it represents
    ///
    /// Returns an error if the string length is of odd parity, or if it
    /// contains any characters that are not valid hexadecimal digits,
    /// insensitive to case.
    pub fn from_hex<S>(hex: &S) -> Result<Self, crate::error::ConvError<String>>
    where
        S: ToOwned<Owned = String> + AsRef<str> + ?Sized,
    {
        match crate::util::bytes_of_hex(hex) {
            Ok(bytes) => Ok(HexString { bytes }),
            Err(HexError(invalid)) => Err(HexError(invalid.to_owned())),
            Err(ParityError(invalid)) => Err(ParityError(invalid.to_owned())),
        }
    }

    /// Returns `true` if `other` is a hex-string that represents the
    /// same byte-sequence as `self`.
    #[must_use]
    pub fn eq_hex<S>(&self, other: &S) -> bool
    where
        S: AsRef<str>,
    {
        other.as_ref().eq_ignore_ascii_case(self.to_hex().as_str())
    }
}

impl From<HexString> for Vec<u8> {
    fn from(val: HexString) -> Self {
        val.bytes
    }
}

impl AsRef<Vec<u8>> for HexString {
    fn as_ref(&self) -> &Vec<u8> {
        &self.bytes
    }
}

impl AsMut<Vec<u8>> for HexString {
    fn as_mut(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }
}

impl AsRef<[u8]> for HexString {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl AsMut<[u8]> for HexString {
    fn as_mut(&mut self) -> &mut [u8] {
        self.bytes.as_mut()
    }
}

impl std::fmt::Debug for HexString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("HexString").field(&self.to_hex()).finish()
    }
}

impl std::fmt::Display for HexString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        String::fmt(&self.to_hex(), f)
    }
}

impl FromIterator<u8> for HexString {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self {
            bytes: <Vec<u8> as FromIterator<u8>>::from_iter(iter),
        }
    }
}

impl Extend<u8> for HexString {
    fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        self.bytes.extend(iter)
    }
}

macro_rules! impl_from {
    ( $src:ty ) => {
        impl From<$src> for HexString {
            fn from(bytes: $src) -> Self {
                Self { bytes }
            }
        }
    };
    ( $src:ty, $meth:ident ) => {
        impl From<$src> for HexString {
            fn from(src: $src) -> Self {
                Self { bytes: src.$meth() }
            }
        }
    };
    ( $lt:lifetime, $src:ty, $meth:ident ) => {
        impl<$lt> From<$src> for HexString {
            fn from(src: $src) -> Self {
                Self { words: src.$meth() }
            }
        }
    };
}

impl_from!(Vec<u8>);
impl_from!(&[u8], to_vec);
impl_from!(Box<[u8]>, to_vec);
impl_from!(std::rc::Rc<[u8]>, to_vec);
impl_from!(std::sync::Arc<[u8]>, to_vec);
impl_from!(std::borrow::Cow<'_, [u8]>, to_vec);

impl std::io::Write for HexString {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.bytes.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.bytes.flush()
    }
}

impl Target for HexString {
    fn anticipate(&mut self, extra: usize) {
        self.bytes.anticipate(extra)
    }

    fn create() -> Self {
        HexString { bytes: Vec::new() }
    }

    fn push_one(&mut self, b: u8) -> usize {
        self.bytes.push_one(b)
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.bytes.push_many(arr)
    }

    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.bytes.push_all(buf)
    }

    fn resolve(&mut self) {
        self.bytes.resolve()
    }
}

macro_rules! impl_try_from {
    ( $src:ty ) => {
        impl TryFrom<$src> for HexString {
            type Error = ConvError<String>;

            fn try_from(s: $src) -> Result<Self, Self::Error> {
                match $crate::util::bytes_of_hex(&s) {
                    Ok(bytes) => Ok(HexString { bytes }),
                    Err(HexError(s)) => Err(HexError(s.to_string())),
                    Err(ParityError(s)) => Err(ParityError(s.to_string())),
                }
            }
        }
    };
}

impl_try_from!(&str);
impl_try_from!(String);
impl_try_from!(std::boxed::Box<str>);
impl_try_from!(std::rc::Rc<str>);
impl_try_from!(std::sync::Arc<str>);
impl_try_from!(std::borrow::Cow<'_, str>);

/// Converts a string-like literal or expression into a HexString by parsing it
/// as hexadecimal
///
/// The argument can be of any type satisfying the bounds:
///
/// ```ignore
/// S: ToOwned<Owned = String> + AsRef<str> + ?Sized
/// ```
///
/// Typically this will be `&str` or `String`, but smart-pointer types
/// [`Box<str>`], [`Rc<str>`], [`Arc<str>`], and [`Cow<'_, str>`] will work as
/// well.
///
/// Will panic if the argument is not a valid hex-string and therefore cannot be
/// converted.
#[macro_export]
macro_rules! hex {
    ($s : expr) => {{
        $crate::hexstring::HexString::from_hex($s).expect("hex! macro encountered error")
    }};
}

impl std::str::FromStr for HexString {
    type Err = crate::error::ConvError<String>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl IntoIterator for HexString {
    type Item = u8;

    type IntoIter = IntoIter<u8>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.bytes.into_iter()
    }
}

macro_rules! impl_partialeq_hexstr {
    ( $other:ty ) => {
        impl PartialEq<HexString> for $other {
            #[inline]
            #[must_use]
            fn eq(&self, other: &HexString) -> bool {
                other.eq_hex(self)
            }
        }

        impl PartialEq<$other> for HexString {
            #[inline]
            #[must_use]
            fn eq(&self, other: &$other) -> bool {
                self.eq_hex(other)
            }
        }
    };
}

// Partial equality between HexString and basic string types
impl_partialeq_hexstr!(&'_ str);
impl_partialeq_hexstr!(String);
impl_partialeq_hexstr!(std::borrow::Cow<'_, str>);
