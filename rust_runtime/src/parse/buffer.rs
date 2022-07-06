//! Common buffer types for `Parser` implementors
//!
//! This module defines the common low-level buffer types
//! used internally by the provided implementors of the
//! [`Parser`] trait.
//!
//! Currently, this includes [`SliceBuffer<'a>`], for `SliceParser<'a>`,
//! and [`VecBuffer`] for [`ByteParser`].
//!
//! [`Parser`]: crate::parse::Parser

use crate::hexstring::HexString;

/// Newtype around a lifetime-annotated immutable slice `&'a [u8]`
///
/// There is no overwhelming motivation for a full newtype,
/// other than to prevent overlapping instances for different interpretations
/// of what sort of role `&[u8]` plays in the context of the runtime.
///
/// In this case, `ByteSlice` is explicitly used only as the buffer type for
/// a slice-based [`Parser`], and is not to be used in place of `&'a [u8]` in
/// any other context.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SliceBuffer<'a>(&'a [u8]);

impl SliceBuffer<'_> {
    /// Creates an explicitly static `SliceBuffer` from a static slice
    pub const fn from_static(slice: &'static [u8]) -> SliceBuffer<'static> {
        SliceBuffer(slice)
    }
}

impl<'a> SliceBuffer<'a> {
    /// Extracts a copy of the internal `&'a [u8]` of a borrowed `SliceBuffer`
    ///
    /// Aside from signature, this is identical to [`into_slice`].
    pub const fn as_slice(&self) -> &'a [u8] {
        self.0
    }

    /// Destructs `self` and returns the `&'a [u8]` it contained
    ///
    /// Aside from signature, this is identical to [`as_slice`].
    pub const fn into_slice(self) -> &'a [u8] {
        self.0
    }

    /// Returns `true` if the `SliceBuffer` has a length of 0
    pub const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of bytes in a `SliceBuffer`.
    #[inline]
    pub const fn len(&self) -> usize {
        self.0.len()
    }

    /// Creates a `SliceBuffer<'a>` from a slice of type `&'a [u8]`
    pub const fn new(slice: &'a [u8]) -> Self {
        Self(slice)
    }

    /// Attempt to extract the first byte of a `SliceBuffer`, returning
    /// both the extracted element and the remainder of the buffer.
    ///
    /// Returns `None` if the `SliceBuffer` is empty
    pub const fn cut_first(&self) -> Option<(u8, Self)> {
        if let [first, tail @ ..] = self.0 {
            Some((*first, Self(tail)))
        } else {
            None
        }
    }

    /// Splits off the head byte of a `ByteSlice` without checking that it is non-empty
    ///
    /// # Safety
    ///
    /// Calling this method on an empty `ByteSlice` is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn cut_first_unchecked(&self) -> (u8, Self) {
        (*self.0.get_unchecked(0), Self(self.0.get_unchecked(1..)))
    }

    /// Splits a `ByteSlice` into the segments containing indices `[0..mid]` and `[mid..]`,
    /// as `ByteSlice`
    ///
    /// This function should behave no differently from [`split_at`][splitat]
    ///
    /// [splitat]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.split_at
    pub fn split(&self, mid: usize) -> (Self, Self) {
        assert!(mid <= self.len());
        unsafe { self.split_unchecked(mid) }
    }

    /// Splits a `ByteSlice` into the segments containing indices `[0..mid]` and `[mid..]`,
    /// as `ByteSlice`, without doing any bounds-checking.
    ///
    /// This is equivalent to [`take_unchecked`] with a wrapped first return value
    ///
    /// # Safety
    ///
    /// Calling this method with `n > self.len()` is *[undefined behavior]*
    /// even if the return value is unused.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn split_unchecked(&self, mid: usize) -> (Self, Self) {
        (
            Self(self.0.get_unchecked(..mid)),
            Self(self.0.get_unchecked(mid..)),
        )
    }

    /// Extracts the first `N` indices of a `ByteSlice` and return them
    /// as a slice, along with the remainder as a `ByteSlice`
    ///
    /// This function is only `unsafe` because it does not itself perform
    /// any slice-length bound-checking and will therefore panic as normal
    /// when the number of indices to take exceeds the number of indices
    /// in the slice itself.
    pub fn take(&self, n: usize) -> (&'a [u8], Self) {
        assert!(n <= self.len());
        unsafe { self.take_unchecked(n) }
    }

    /// Extracts the first `len` indices of a `ByteSlice` unwrapped,
    /// along with the remainder as a `ByteSlice`, without
    /// doing bounds-checking.
    ///
    /// For a safe alternative see [`take`]
    ///
    /// # Safety
    ///
    /// Calling this method with `n > self.len()` is *[undefined behavior]*
    /// even if the return value is unused.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn take_unchecked(&self, n: usize) -> (&'a [u8], Self) {
        (self.0.get_unchecked(..n), Self(self.0.get_unchecked(n..)))
    }
}

impl<'a> From<&'a [u8]> for SliceBuffer<'a> {
    #[inline]
    fn from(bytes: &'a [u8]) -> Self {
        Self(bytes)
    }
}

/// Newtype around `Vec<u8>` that only permits immutable access
///
/// This newtype is used to allow for explicit signalling of intended role for
/// the use of `Vec<u8>` as the underlying, immutable buffer of a [`ByteParser`]
/// or equivalent-model `Parser` implementation.
///
/// The contents of a `VecBuffer` are not mutated by any of the inherent methods
/// defined in this module.
///
/// [`ByteParser`]: crate::parse::byteparser::ByteParser
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct VecBuffer(Vec<u8>);

impl VecBuffer {
    /// Returns the number of bytes in a `VecBuffer`
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the buffer contains zero bytes
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Borrows a range of bytes starting at index `ix`, of length `len`,
    /// without bounds-checking.
    ///
    /// # Safety
    ///
    /// Calling this method when `[ix..ix + len]` is not in-bounds is
    /// *[undefined behavior]* even if the return value is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn get_slice_unchecked(&self, ix: usize, len: usize) -> &[u8] {
        self.0.get_unchecked(ix..ix + len)
    }

    /// Borrows a range of bytes starting at index `ix`, of length `len`.
    ///
    /// # Panics
    ///
    /// Will panic if `ix + len` is out-of-bounds
    pub fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
        assert!(ix + len <= self.len());
        unsafe { self.get_slice_unchecked(ix, len) }
    }

    /// Returns the byte at the specified index without checking that it is in-bounds.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bonds index is
    /// *[undefined behavior]* even if the return value is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    pub unsafe fn get_byte_unchecked(&self, ix: usize) -> u8 {
        *self.0.get_unchecked(ix)
    }

    /// Returns the byte at the specified index,
    ///
    /// # Panics
    ///
    /// Will panic if the `ix` is out-of-bounds
    pub fn get_byte(&self, ix: usize) -> u8 {
        assert!(ix <= self.len());
        unsafe { self.get_byte_unchecked(ix) }
    }
}

impl std::fmt::Debug for VecBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Vec<u8> as std::fmt::Debug>::fmt(&self.0, f)
    }
}

impl From<&[u8]> for VecBuffer {
    fn from(bytes: &[u8]) -> Self {
        Self(bytes.to_owned())
    }
}

impl From<Vec<u8>> for VecBuffer {
    fn from(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }
}

impl<const N: usize> From<[u8; N]> for VecBuffer {
    fn from(bytes: [u8; N]) -> Self {
        Self(bytes.to_vec())
    }
}

impl<const N: usize> From<&'_ [u8; N]> for VecBuffer {
    fn from(bytes: &'_ [u8; N]) -> Self {
        Self(bytes.to_vec())
    }
}

impl From<HexString> for VecBuffer {
    fn from(hex: HexString) -> Self {
        Self(hex.into_inner())
    }
}

macro_rules! string_to_vecbuffer {
    ( $src:ty ) => {
        #[cfg(feature = "implicit_hexstring")]
        impl std::convert::TryFrom<$src> for $crate::parse::buffer::VecBuffer
        where
            $crate::hexstring::HexString: std::convert::TryFrom<$src>,
            Self: From<$crate::hexstring::HexString>,
        {
            type Error = <$src as std::convert::TryInto<$crate::hexstring::HexString>>::Error;

            fn try_from(s: $src) -> Result<Self, Self::Error> {
                Ok(<HexString as std::convert::TryFrom<$src>>::try_from(s)?.into())
            }
        }

        #[cfg(not(feature = "implicit_hexstring"))]
        impl From<$src> for $crate::parse::buffer::VecBuffer {
            fn from(s: $src) -> Self {
                Self(s.as_bytes().to_owned())
            }
        }
    };
    (  $src:ty, $lt:lifetime ) => {
        #[cfg(feature = "implicit_hexstring")]
        impl<$lt> std::convert::TryFrom<$src> for $crate::parse::buffer::VecBuffer
        where
            $crate::hexstring::HexString: std::convert::TryFrom<$src>,
            Self: From<$crate::hexstring::HexString>,
        {
            type Error = <$crate::hexstring::HexString as std::convert::TryFrom<$src>>::Error;

            fn try_from(s: $src) -> Result<Self, Self::Error> {
                Ok(
                    <$crate::hexstring::HexString as std::convert::TryFrom<$src>>::try_from(s)?
                        .into(),
                )
            }
        }

        #[cfg(not(feature = "implicit_hexstring"))]
        impl<$lt> From<$src> for $crate::parse::buffer::VecBuffer {
            fn from(s: $src) -> Self {
                Self(s.as_bytes().to_owned())
            }
        }
    };
}

string_to_vecbuffer!(&'a str, 'a);
string_to_vecbuffer!(String);
string_to_vecbuffer!(&'a String, 'a);
string_to_vecbuffer!(std::borrow::Cow<'a, str>, 'a);
