//! Validated conversion to and from hex-encoded strings
//!
//! # Background
//!
//! For reasons of cross-language portability, as well as human readability,
//! it is common practice within `data-encoding`-based projects (notably, Octez)
//! to represent the serialized bytes of an encoded value as a *hex-string*, rather
//! than as a raw bytestring that directly represents the byte-for-byte binary data.
//!
//! By *hex-string* in this context, we mean a string of ASCII characters,
//! matching the regular expression `([0-9a-fA-F]{2})*`. Neither lower, upper,
//! or even consistent case is enforced at this layer, and two strings that
//! are equivalent up to case represent identical data.
//!
//! Each aligned pair of characters represents a single byte in the corresponding
//! position, whose value is precisely the interpretation of the pair as a hex-encoded
//! byte: `"deadbeef" ~ [0xde, 0xad, 0xbe, 0xef]`
//!
//! As it stands, there is no unambiguously obvious default interpretation for
//! character-based strings, at the level of serialized values to be decoded;
//! an argument could be made either for interpretation as raw binary, or as
//! a hex-encoded string. The following two options are incompatible, but both
//! can be fairly easily justified interfaces:
//!
//!   * `decode("deadbeef") == decode(b"deadbeef")`
//!   * `decode("deadbeef") == decode([0xde, 0xad, 0xbe, 0xef])`
//!
//! That is to say, while it is far more portable to use the latter, which
//! allows for all byte-values from `0` to `255` to be represented,
//! it might be natural for an end-user to assume the former, even if it
//! is less sound as a general approach.
//!
//! # `HexString`
//!
//! The struct `HexString` defined in this module provides an unambiguous
//! solution to this dichotomy. A `HexString` can be created from:
//!
//!   * String-like types: `&str`, `String`, `Cow<'_, str>`, etc.
//!   * Byte-array-like types: `[u8; N]`, `&[u8]`, `Vec<[u8]>`, etc.
//!
//! In either case, however, there is no ambiguity as to how a type is
//! to be interpreted; `From` is implicitly binary-based, and `TryFrom`
//! is a fallible parse from hex-encoded data.
//!
//! # Parsing
//!
//! Given a `String`, `&str`, or similar value, the only stable way to
//! ensure that it is parsed as a hex-string is to convert it to a `HexString`,
//! using either `HexString::from_hex()` or
//!
//! For lightweight construction of `HexString` values from string-like
//! values, the [`hex`] macro is also provided, which works on the
//! majority of string-like types.

use crate::conv::target::Target;
use crate::error::ConvError::{self, HexError, ParityError};
use std::{convert::TryFrom, iter::FromIterator};

pub use std::vec::IntoIter;

pub type Iter<'a> = std::slice::Iter<'a, u8>;

pub(crate) mod util {
    use crate::error::ConvError;
    use std::fmt::Write;

    /// Formats a sequence of bytes into an undelimited hexadecimal `String`
    ///
    /// Works generically over any argument type that implements `AsRef<[u8]>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::util::hex_of_bytes;
    /// assert_eq!(hex_of_bytes(vec![0xde,0xad,0xbe,0xef]), String::from("deadbeef"));
    /// ```
    #[must_use]
    #[inline]
    pub fn hex_of_bytes(bytes: &[u8]) -> String {
        let mut hex: String = String::with_capacity(bytes.len() * 2);
        for &byte in bytes {
            match write!(&mut hex, "{byte:02x}") {
                Ok(_) => (),
                Err(_) => unreachable!("write to String should never fail"),
            };
        }
        hex
    }

    /// Attempt to parse a hexadecimally encoded string-like type, returning either
    /// a `Vec<u8>` holding the decoded bytes or an error containing the invalid
    /// string.
    ///
    /// # Errors
    ///
    /// If the referenced string (via `AsRef<str>`) has odd parity,
    /// `Err(ParityError)` is returned.
    ///
    /// Otherwise, if the string contains any character that is not a valid
    /// hexadecimal digit (case-insensitive), returns `Err(HexError(s))` where `s`
    /// is the string in question.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::util::bytes_of_hex;
    /// assert_eq!(Ok(vec![0xde,0xad,0xbe,0xef]), bytes_of_hex("deadbeef"));
    /// ```
    ///
    #[inline]
    pub fn bytes_of_hex(src: &str) -> Result<Vec<u8>, ConvError<&str>> {
        let ascii_len = src.len();

        if ascii_len == 0 {
            return Ok(Vec::new());
        } else if ascii_len % 2 != 0 {
            return Err(ConvError::ParityError(src));
        }

        let mut dst = Vec::with_capacity(ascii_len / 2);

        for ix in (0..ascii_len).step_by(2) {
            match u8::from_str_radix(&src[ix..ix + 2], 16) {
                Ok(word) => dst.push(word),
                Err(_) => return Err(ConvError::HexError(src)),
            }
        }
        Ok(dst)
    }

    /// Zero-alloc short-circuiting equality test between hex-strings and
    /// byte-arrays
    ///
    /// Returns `true` if `src` represents a valid hexadecimal encoding of `tgt`,
    /// and `false` otherwise, including when `src` is not valid hex.
    ///
    /// In terms of semantics, equivalent to a case-insensitive string equality
    /// test between `src` and `hex_of_bytes(tgt)`, or a direct equality test
    /// between `bytes_of_hex(src)` and `tgt`. However, this function is short-circuiting
    /// and does not require any heap allocations, and therefore is more efficient
    /// than either of those two alternate approaches.
    #[inline]
    #[must_use]
    pub fn eq_hex_bytes(src: &str, tgt: &[u8]) -> bool {
        let ascii_len: usize = src.len();
        let bytes_len: usize = tgt.len();

        if bytes_len * 2 != ascii_len {
            return false;
        }

        if ascii_len == 0 {
            return true;
        }

        let mut pat = tgt;

        for ix in (0..ascii_len).step_by(2) {
            if let &[head, ref tail @ ..] = pat {
                match u8::from_str_radix(&src[ix..ix + 2], 16) {
                    Ok(word) if word == head => (),
                    _ => return false,
                }
                pat = tail;
            }
        }
        pat.is_empty()
    }
}

/// Newtype representing byte-arrays that are parsed from and displayed as
/// hexadecimally encoded `String` values, but stored in memory as byte-buffers
/// representing the individual words parsed from the string.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
#[repr(transparent)]
pub struct HexString {
    bytes: Vec<u8>,
}

impl HexString {
    /// Extracts a slice containing the entirety of the underlying vector
    ///
    /// Equivalent to `self.as_vec().as_slice()`
    ///
    /// # Examples
    /// ```
    /// # use rust_runtime::hexstring::HexString;
    /// let h = HexString::
    ///
    ///
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

    /// Extracts a mutable reference to the underlying vector
    pub fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }

    /// Extracts a reference to the underlying vector
    pub const fn as_vec(&self) -> &Vec<u8> {
        &self.bytes
    }

    /// Constructs a `HexString` from an existing `Vec<u8>` without copying
    /// or cloning.
    ///
    ///
    #[inline]
    #[must_use]
    pub fn from_vec(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    /// Destructs a `HexString` into its underlying byte-vector
    #[inline]
    #[must_use]
    pub fn into_vec(self) -> Vec<u8> {
        self.bytes
    }

    /// Returns `true` if the `HexString` has length 0
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns the number of bytes in `self`
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Constructs a new, empty `HexString`
    ///
    /// Until it is written to, the underlying vector will remain unallocated.
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self { bytes: Vec::new() }
    }
}

impl HexString {
    /// Constructs a new `HexString` around a newly allocated
    /// `Vec<u8>` containing the bytes of `src.as_ref()`.
    ///
    /// When `T` implements `Into<Vec<u8>>` in such a way that
    /// this implicit copying is not necessary, use
    /// [`from_bytes`] instead.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::{hex, hexstring::HexString};
    /// assert_eq!(hex!("deadbeef"), HexString::clone_from_bytes([0xde, 0xad, 0xbe, 0xef]));
    /// ```
    #[must_use]
    pub fn clone_from_bytes<T>(src: T) -> Self
    where
        T: AsRef<[u8]>,
    {
        Self {
            bytes: src.as_ref().to_vec(),
        }
    }

    /// Constructs a new `HexString` whose underlying vector
    /// is simply `<T as Into<Vec<u8>>>::into` applied to the
    /// provided argument.
    ///
    /// Notably, this should be optimized into a move when
    /// `T` happens to be a `Vec<u8>`.
    ///
    /// For a version that works more broadly on any type that
    /// can be coerced into `&[u8]` via the [`AsRef`] trait,
    /// see [`clone_from_bytes`], which may be less efficient
    /// than `from_bytes` for types that satisfy the trait bounds
    /// of both methods.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::{hex, hexstring::HexString};
    /// assert_eq!(hex!("deadbeef"), HexString::from_bytes(vec![0xde, 0xad, 0xbe, 0xef]));
    /// ```
    #[must_use]
    pub fn from_bytes<T>(bytes: T) -> Self
    where
        Vec<u8>: From<T>,
    {
        Self {
            bytes: bytes.into(),
        }
    }

}

impl HexString {
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
        util::hex_of_bytes(&self.bytes)
    }

    /// Attempt to parse a hexadecimally encoded string into the sequence of
    /// bytes it represents
    ///
    /// Returns an error if the string length is of odd parity, or if it
    /// contains any characters that are not valid hexadecimal digits,
    /// insensitive to case.
    pub fn from_hex<S>(hex: S) -> Result<Self, crate::error::ConvError<String>>
    where
        S: AsRef<str>,
    {
        Ok(Self {
            bytes: util::bytes_of_hex(hex.as_ref()).map_err(ConvError::to_owned)?,
        })
    }

    /// Returns `true` if `other` is a hex-string that represents the
    /// same byte-sequence as `self`.
    ///
    /// Returns `false` when `other` is either a valid hex-string that
    /// is not equal to `self`, or when `other` is not a valid hex-string.
    #[must_use]
    pub fn eq_hex<S>(&self, other: &S) -> bool
    where
        S: AsRef<str> + ?Sized,
    {
        util::eq_hex_bytes(other.as_ref(), self.as_bytes())
    }
}

impl HexString {
    /// Returns an iterator over the bytes of `self`
    ///
    /// # Examples
    ///
    /// ```
    /// # use rust_runtime::{hex, hexstring::HexString};
    /// let h : HexString = hex!("deadbeef");
    /// let mut i = h.iter();
    /// assert_eq!(i.next(), Some(&0xde));
    /// assert_eq!(i.next(), Some(&0xad));
    /// assert_eq!(i.next(), Some(&0xbe));
    /// assert_eq!(i.next(), Some(&0xef));
    /// assert_eq!(i.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        self.bytes.iter()
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

impl IntoIterator for HexString {
    type Item = u8;

    type IntoIter = IntoIter<u8>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.bytes.into_iter()
    }
}

impl<'a> IntoIterator for &'a HexString {
    type Item = &'a u8;

    type IntoIter = Iter<'a>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

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

impl From<HexString> for Vec<u8> {
    fn from(val: HexString) -> Self {
        val.bytes
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
    ( $cg:ident, $src:ty, $meth:ident ) => {
        impl<const $cg: usize> From<$src> for HexString {
            fn from(src: $src) -> Self {
                Self { bytes: src.$meth() }
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

impl_from!(N, [u8; N], to_vec);
impl_from!(N, &[u8; N], to_vec);
impl_from!(N, Box<[u8; N]>, to_vec);
impl_from!(N, std::rc::Rc<[u8; N]>, to_vec);
impl_from!(N, std::sync::Arc<[u8; N]>, to_vec);
impl_from!(N, std::borrow::Cow<'_, [u8; N]>, to_vec);


macro_rules! impl_try_from {
    ( $src:ty ) => {
        impl TryFrom<$src> for HexString {
            type Error = ConvError<String>;

            fn try_from(s: $src) -> Result<Self, Self::Error> {
                match $crate::hexstring::util::bytes_of_hex(&s) {
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
