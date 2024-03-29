//! Wrapper types for variable-length values
//!
//! This module provides wrapper types that model the two constructs used for
//! handling unambiguous parsing of schema elments of variable binary length.
//!
//! # Dynamic Wrappers
//!
//! ## [`Dynamic<S, T>`]
//!
//! The primary, and far more general-purpose approach used, is
//! to precede a variable-length component with a length-prefix
//! indicating, as an unsigned integer, how many bytes said
//! component occupies. Such a prefix is either 1, 2, or 4 bytes in length, corresponding to the ranges
//! of `u8`, `u16`, and [`u30`][uthirty] (and not, in fact, `u32`).
//!
//! Accordingly, this module defines the type `Dynamic<S, T>`, which
//! represents a value of payload type `T` that is encoded and decoded
//! using a prefix of type `S` satisfying the trait bound of [`LenPref`].
//! Said trait is also defined in this module, and sealed, with only three
//! implementing types: [`u8`], [`u16`], and [`u30`][uthirty]
//!
//! ## [`VPadded<T, N>`]
//!
//! In certain cases, variable-length schema elements appearing within
//! a surrounding contents whose total length is known, may be encoded
//! and decoded transparently, provided that the combined length of
//! all subsequent elements in the same context is a known constant.
//!
//! To handle such cases, a wrapper type `VPadded<T, N>` is defined,
//! which represents a payload value `T` that is followed, in the innermost
//! context in which it appears, by exactly `N` total bytes of subsequent
//! values.
//!
//! In terms of serialization via the [`Encode`] trait, `VPadded<T, N>`
//! is identical to `T`. In terms of deserialization, `VPadded<T, N>`
//! acts as a 'virtually padded'
//! version of `T`: a novel context is spawned that covers all but
//! the last `N` bytes of the current context, and the parsing of `T` is
//! bound to the limited context. Provided that `T` parses successfully in
//! this restricted view, this limit is removed so that the subsequent
//! elements can parse the final `N` bytes of the original view.
//!
//! # Generic Order
//!
//! It may be slightly counter-intuitive that, while in both `VPadded<T, N>`
//! and `Dynamic<S, T>`, `T` is the payload type, it appears as the first
//! parameter for the former and the second for the latter. It is suggested
//! that this choice is perhaps more intuitive than a consistent order:
//! namely, `Dynamic<S, T>` is encoded with a value of type `S` preceding
//! the payload and therefore `S` is the first generic paramter; and for
//! `VPadded<T, N>`, `N` represents the number of bytes following `T`,
//! and is therefore the second genreic paramter.
//!
//! The names for the parameters in question, and the order in which they
//! appear, may be subject to change in later releases.
//!
//! [uthirty]: crate::int::u30

use crate::conv::len::{Estimable, FixedLength};
use crate::conv::{Decode, Encode, EncodeLength};
use crate::int::u30;
use crate::parse::{ParseResult, Parser};
use std::borrow::Borrow;
use std::convert::TryFrom;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::marker::PhantomData;

/// `Dynamic<S, T>`: Schema-level construct for explicit dynamic length of variable-length types
///
/// Consists of a payload of type `T`, preceded by a length-prefix of the
/// specified unsigned integral type `S`. The value of the `S`-typed prefix
/// indicates the exact number of bytes in the payload of type `T`.
///
/// The generic parameter `S` must implement the trait `LenPref`, which is
/// marked unsafe as it is a closed class containing only [`u8`], [`u16`],
/// and [`u30`](crate::int::u30).

#[derive(Clone, Copy)]
pub struct Dynamic<S: LenPref, T> {
    contents: T,
    _phantom: PhantomData<S>,
}

impl<S: LenPref, T> Dynamic<S, T> {
    /// Wraps a value of type `T` into a `Dynamic<S, T>` object.
    ///
    /// This is mostly useful when attempting to fit a variable-length value
    /// of type `T` into a codec type in which it appears in the form `Dynamic<S, T>`
    /// for some `S`.
    ///
    /// Note that the value to be wrapped is not length-checked
    /// to ensure it can be serialized in no fewer than `M` bytes,
    /// where `M` is the maximum value in the range of `S`;
    /// this check is only done during the encoding step, and
    /// will result in a panic if this condition is violated.
    #[inline]
    #[must_use]
    pub fn new(contents: T) -> Self {
        Self {
            contents,
            _phantom: PhantomData,
        }
    }

    /// Destructor for `Dynamic<S, T>` that returns the contained
    /// payload of type `T`.
    ///
    /// This is mostly useful when attempting to extract the payload
    /// values from a codec type that holds `Dynamic<S, T>`, after
    /// the codec type has been decoded.
    #[inline]
    #[must_use]
    pub fn into_inner(self) -> T {
        self.contents
    }

    /// Attempt to represent the binary width of the payload `T`-value of `self`
    /// in the range of the length-prefix type `S`.
    ///
    /// # Errors
    ///
    /// If the number of bytes in `T` exceeds the maximum legal value of `S`,
    /// `WidthError::TooWide` is returned.
    #[inline]
    pub fn length_prefix(&self) -> Result<S, crate::error::WidthError>
    where
        T: EncodeLength,
    {
        let actual: usize = <T as EncodeLength>::enc_len(&self.contents);
        match S::try_from(actual) {
            Ok(x) => Ok(x),
            Err(_err) => {
                let limit: usize = S::max_len();
                debug_assert!(
                    actual > limit,
                    "unexpected Err in {}::try_from({actual})",
                    <S as LenPref>::suffix(),
                );
                Err(crate::error::WidthError::TooWide { limit, actual })
            }
        }
    }
}

impl<S: LenPref, T> PartialOrd for Dynamic<S, T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.contents.partial_cmp(&other.contents)
    }
}

impl<S: LenPref, T> Ord for Dynamic<S, T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.contents.cmp(&other.contents)
    }
}

impl<S: LenPref, T> PartialEq for Dynamic<S, T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.contents.eq(&other.contents)
    }
}

impl<S: LenPref, T> Eq for Dynamic<S, T> where T: Eq {}

impl<S: LenPref, T> Hash for Dynamic<S, T>
where
    T: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.contents.hash(state);
    }
}

impl<S: LenPref, T> Borrow<T> for Dynamic<S, T> {
    fn borrow(&self) -> &T {
        &self.contents
    }
}

impl<S: LenPref, T> AsRef<T> for Dynamic<S, T> {
    fn as_ref(&self) -> &T {
        &self.contents
    }
}

impl<S: LenPref, T> AsMut<T> for Dynamic<S, T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.contents
    }
}

impl<S: LenPref, T: Estimable> Estimable for Dynamic<S, T> {
    const KNOWN: Option<usize> = {
        let x = S::KNOWN;
        let y = T::KNOWN;
        match (x, y) {
            (Some(m), Some(n)) => Some(m + n),
            _ => None,
        }
    };

    #[inline]
    fn unknown(&self) -> usize {
        <S as FixedLength>::LEN + self.contents.unknown()
    }
}

impl<S: LenPref, T: Debug + EncodeLength> Debug for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}{} bytes|{:?}]",
            self.contents.enc_len(),
            S::suffix(),
            self.contents
        )
    }
}

/// Display implementation for `Dynamic<S, T>`
///
/// Displays `Dynamic<S, T>` by-value using `T: Display`, without
/// indicating that it is wrapped, or the type of the prefix.
impl<S: LenPref, T: Display> Display for Dynamic<S, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.contents, f)
    }
}

impl<S: LenPref, T> From<T> for Dynamic<S, T> {
    fn from(val: T) -> Self {
        Self {
            contents: val,
            _phantom: std::marker::PhantomData,
        }
    }
}

/// Marker trait for the suitability as dynamic length prefix
///
/// `LenPref` is a sealed trait used as a bound on the phantom parameter `S` of [`Dynamic<S,T>`].
///
/// Specifically, the only valid implementors are [`u8`], [`u16`], and [`u30`](crate::int::u30).
///
/// As this is a closed trait, it is made public for use as a valid trait-bound on the public type
/// `Dynamic`, but is sealed via a private empty supertrait. It is therefore not possible for any external
/// code to implement `LenPref`.
///
/// In addition to being a marker, this trait also presents the necessary bounds shared by the three
/// valid length-prefix types: infallible coercion to and fallible conversion from `usize`, `Copy`,
/// [`Encode`](crate::conv::Encode) (via [`EncodeLength`](crate::conv::EncodeLength)), [`Decode`](crate::conv::Decode),
/// and [`FixedLength`](crate::conv::len::FixedLength).
pub trait LenPref
where
    Self:
        Into<usize> + TryFrom<usize> + Copy + EncodeLength + Decode + FixedLength + private::Sealed,
{
    fn parse_as_usize<P: Parser + ?Sized>(p: &mut P) -> ParseResult<usize> {
        let raw_bytes = p.consume(Self::LEN)?;
        unsafe { Ok(Self::marshall_usize(raw_bytes)) }
    }

    /// Returns a `uX`-style name for LenPref, as is common for writing
    /// explicitly-typed integer literals
    fn suffix() -> &'static str {
        std::any::type_name::<Self>()
    }

    /// Returns the maximum number of bytes of payload supported
    /// by a particular `LenPref` type, as a `usize`
    fn max_len() -> usize;
}
mod private {
    pub trait Sealed {
        unsafe fn marshall_usize(bytes: &[u8]) -> usize;
    }

    impl Sealed for u8 {
        unsafe fn marshall_usize(bytes: &[u8]) -> usize {
            let bytes = <[u8; 1]>::try_from(bytes).unwrap_unchecked();
            let raw = Self::from_be_bytes(bytes);
            raw as usize
        }
    }

    impl Sealed for u16 {
        unsafe fn marshall_usize(bytes: &[u8]) -> usize {
            let bytes = <[u8; 2]>::try_from(bytes).unwrap_unchecked();
            let raw = Self::from_be_bytes(bytes);
            raw as usize
        }
    }

    impl Sealed for crate::int::u30 {
        unsafe fn marshall_usize(bytes: &[u8]) -> usize {
            let bytes = <[u8; 4]>::try_from(bytes).unwrap_unchecked();
            let raw = i32::from_be_bytes(bytes);
            let _ = crate::int::u30::try_from_i32(raw)
                .expect("Inherent conversion from i32->u30 failed");
            raw as usize
        }
    }
}

impl LenPref for u8 {
    /// Maximum byte-length representable within the range of a `u8`, as a `usize`
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::tedium::dynamic::LenPref;
    /// assert_eq!(<u8 as LenPref>::max_len(), (1usize << 8) - 1);
    /// ```
    fn max_len() -> usize {
        u8::MAX as usize
    }
}

impl LenPref for u16 {
    /// Maximum byte-length representable within the range of a `u16`, as a `usize`
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::tedium::dynamic::LenPref;
    /// assert_eq!(<u16 as LenPref>::max_len(), (1usize << 16) - 1);
    /// ```
    fn max_len() -> usize {
        u16::MAX as usize
    }
}
impl LenPref for u30 {
    fn suffix() -> &'static str {
        "u30"
    }

    /// Maximum byte-length representable within the range of a `u30`, as a `usize`
    ///
    /// # Examples
    ///
    /// ```
    /// # use ::tedium::{dynamic::LenPref, int::u30};
    /// assert_eq!(<u30 as LenPref>::max_len(), (1usize << 30) - 1);
    /// ```
    fn max_len() -> usize {
        u30::MAX as usize
    }
}

impl<S: LenPref, T: EncodeLength> Encode for Dynamic<S, T> {
    /// Writes the contents of type `T` of a `Dynamic<S, T>`,
    /// prepending a prefix of type `S` indicating how many bytes
    /// it occupies.
    ///
    /// # Panics
    ///
    /// This function panics if the serialization of `T` exceeds the
    /// maximum representable value of type `S`, indicating that the
    /// value of the type is unsound.
    ///
    fn write_to<U: crate::conv::target::Target>(&self, buf: &mut U) -> usize {
        let l: usize = self.contents.enc_len();
        assert!(
            l <= S::max_len(),
            "payload length {} unrepresentable as {}",
            l,
            S::suffix(),
        );
        match S::try_from(l) {
            Ok(lp) => {
                buf.anticipate(l + <S as EncodeLength>::enc_len(&lp));
                crate::write_all_to!(lp, self.contents => buf)
            }
            Err(_) => unreachable!(),
        }
    }
}

impl<S: LenPref, T: Decode> Decode for Dynamic<S, T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buflen = S::parse(p)?;
        p.set_fit(buflen.into())?;
        let contents = T::parse(p)?;
        p.enforce_target()?;
        Ok(Self::new(contents))
    }
}

/// `VPadded<T, N>`: Wrapper type around `T` that virtually "pads" it with `N`
/// bytes for the purposes of determining when a variable-length field (or tuple
/// positional argument) terminates.
///
/// A value of type `VPadded<T, N>` is semantically equivalent to a value of
/// type `T` for almost any purpose, except for the purposes of parsing. In
/// particular, when a value of type `VPadded<T, N>` has been fully parsed (and
/// does not panic or otherwise fail), there will be exactly `N` unparsed bytes
/// left in the current surrounding parse-context, which have been reserved for
/// a fixed-length tail of remaining fields or arguments in a record or
/// tuple-like container.
///
/// In terms of syntax, `VPadded<T, N>` is similar to [`Padded<T,
/// N>`](crate::schema::Padded), though the operational semantics of the two
/// with respect to encoding and decoding are entirely distinct.
///
/// It is technically valid to have a value of type `VPadded<_, 0>` just as it
/// is valid to have a value of type `Padded<_, 0>`, though neither one is
/// expected to appear in codecs as they are fundamentally indistinguishable
/// from the payload type, and each other, for the purposes of encoding and
/// decoding.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default)]
#[repr(transparent)]
pub struct VPadded<T, const N: usize>(T);

impl<T: Debug, const N: usize> Debug for VPadded<T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <T as Debug>::fmt(&self.0, f)
    }
}

impl<T, const N: usize> VPadded<T, N> {
    /// Wraps a value of type `T` into a `VPadded<T, N>` object.
    ///
    /// This is mostly useful when attempting to fit raw values
    /// into a codec type that expects `VPadded<T, N>`, to be
    /// encoded.
    pub fn new(val: T) -> Self {
        Self(val)
    }

    /// Destructor for `VPadded<T, N>` that returns the contained
    /// payload of type `T`.
    ///
    /// This is mostly useful when attempting to extract the payload
    /// values from a codec type that holds `VPadded<T, N>`, after
    /// the codec type has been decoded.
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T, const N: usize> From<T> for VPadded<T, N> {
    fn from(val: T) -> Self {
        Self(val)
    }
}

impl<T: Encode, const N: usize> Encode for VPadded<T, N> {
    fn write_to<U: crate::Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf)
    }
}

impl<T: Decode, const N: usize> Decode for VPadded<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let _rem = p.remainder();
        debug_assert!(
            _rem >= N,
            "Cannot parse VPadded<{}, {}> with {} (< {}) bytes remaining",
            std::any::type_name::<T>(),
            N,
            _rem,
            N
        );
        p.set_fit(_rem - N)?;
        let ret = T::parse(p)?;
        p.enforce_target()?;
        Ok(Self(ret))
    }
}

impl<T: Estimable, const N: usize> Estimable for VPadded<T, N> {
    const KNOWN: Option<usize> = T::KNOWN;

    fn unknown(&self) -> usize {
        self.0.unknown()
    }
}
