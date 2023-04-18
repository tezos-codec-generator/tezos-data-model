//! Specialized schema types
//!
//! For certain constructors within the `data-encoding` schema language,
//! it is necessary to define custom codec types within this crate to
//! ensure that the intended serialization layout is preserved. Most
//! such definitions consist of newtypes patterns around existing Rust-native
//! types, which distinguish their intended use-case and allow for specialized
//! serialization logic, when there is information in the wrapping type that
//! leads to a modified binary encoding compared to the type being wrapped.
//!
//! This module contains an assortment of such type definitions, as well as
//! implementations of both library-defined, and common `std` traits as
//! appropriate.
//!
//! # `Padded<T, N>`
//!
//! [`Padded<T, N>`] represents a value of type `T` with `N` bytes of additional
//! (post-)padding, which are expected, but not required, to be [NIL]. This is
//! commonly found as a wrapper around the last element of a record-like enum-type
//! variant, whose nominal serialization length is extended to match that of a
//! wider variant.
//!
//! # `Bytes`
//!
//! [`Bytes`] is a variable-length byte-sequence whose contents are otherwise opaque.
//! It may appear in codecs whose original schema uses the `conv` combinator to
//! further interpret a series of context-sensitive values from this byte-sequence,
//! or, alternatively, for variable-length signatures, hashes, and other raw data
//! with no further refinement.
//!
//! `Bytes` is the variable-length analogue of the fixed-length type
//! [`FixedBytes<N>`](crate::fixed::bytes::FixedBytes), which includes
//! a const generic parameter `N: usize` that indicates its exact width.
//!
//! # `Nullable<T>`
//!
//! Optional fields in `data-encoding` are encoded in one of two possible ways, based
//! on certain contextual optimizations.
//!
//! For the majority of cases, they are encoded with a one-byte boolean flag indicating
//! whether the field is present (for `0xff ~ true`) or absent (for `0x00 ~ false`).
//! Accordingly, the more convenient model of [`std::option::Option<T>`] is used for such
//! cases, and the blanket implemenations of [`Encode`] and [`Decode`] over `Option<T>`
//! use this behavior.
//!
//! In certain cases, the encoding of optional fields may leave off this one-byte flag,
//! which will typically be limited to those contexts in which a zero-width element
//! appearing in the corresponding position can be inferred just before the optional
//! field in question would be parsed. A common example is when this is the final field
//! in a record, or when the total byte-width of all subsequent fields is a known constant
//! value.
//!
//! As such cases are less common, a custom type [`Nullable<T>`] is provided, which is
//! implemented as a newtype around `Option<T>`. In terms of serialization, `Nullable(Some(x))`
//! is equivalent to `x`, and `Nullable(None)` is a zero-width element.
//!
//! # Sequence Types
//!
//! The submodule `seq` provides definitions for sequence-types:
//!   - Unbounded-length: [`Sequence<T>`]
//!   - Bounded-length: [`LimSeq<T>`]
//!   - Fixed-length: [`FixSeq<T>`]
//!
//! The organization of these types, and assorted schema-specific types
//! currently defined in separate modules, may be subject to change as the
//! library evolves.

use crate::conv::target::Target;
use crate::conv::{len::Estimable, Decode, Encode};
use crate::parse::{ParseResult, Parser};
#[cfg(feature = "serde_impls")]
use serde::Serialize;
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};

/// Wrapper around a `T` value that writes/reads `N` subsequent bytes of padding
///
/// The `Padded<T, N>` type is a direct analogue to the `Padded` constructor in the `data-encoding` library
/// binary-schema AST. It is a shallow wrapper around an inner value of type `T`.
/// `Padded<T, N>` is encoded as the inner value `T: Encode`, with `N` additional
/// `NIL`-valued bytes written subsequently. Correspondingly, it is deserialized
/// by reading a value of type `T` and consuming (or otherwise skipping) `N` bytes.
///
/// # Invariants
///
/// It is an undocumented invariant on the original `Padded` constructor in
/// `data-encoding` that the encoding being padded must be of fixed (constant)
/// serialization width. This detail may change in future versions, however, and
/// it is difficult to statically enforce a bound of fixed-width serialization
/// on custom types without more complex logic in the generator.
///
/// Attempting to create or manipulate a `Padded<T, N>` value where `T` is not
/// of constant binary width (according to [`Estimable::KNOWN`]) is considered
/// **undefined behavior**, provided that the feature
/// `relaxed_padding_invariant` is not enabled.
///
/// # Padding Bytes
///
/// The current implementation of deserialization logic in `data-encoding` does
/// not check that the extra padding bytes are all `NIL`-valued. Rather than
/// a license to use arbitrary bytes as padding, this is best thought of as a
/// an optimization that assumes the expected case, which would otherwise incur
/// a performance overhead to check, and would not necessarily imply unsoundness
/// even if it were violated.
///
/// Unless overridden by optional feature flags, the deserialization logic in
/// this crate likewise skips NIL-checking of the padding bytes, and will return
/// successfully provided that the expected number of padding bytes could be
/// consumed, regardless of their actual value.
///
/// Client libraries using this crate may opt into NIL-checking via the
/// `check_padding` feature, which is disabled by default.  Doing so will incur
/// a slight performance overhead during the decoding of `Padded<T, N>` values,
/// but will potentially catch bugs that might otherwise go unnoticed, or
/// manifest later on as difficult-to-diagnose errors.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default)]
#[repr(transparent)]
pub struct Padded<T, const N: usize>(T);

impl<T, const N: usize> Padded<T, N> {
    /// A type-associated constant representing the number of bytes of padding.
    ///
    /// This is primarily useful to determine the generic `N` in `Padded<T, N>`
    /// across type-aliases where it is not explicitly in scope.
    pub const PADDING: usize = N;

    /// Constructs a new value of type `Padded<T, N>` containing a payload `x`
    #[inline]
    #[must_use]
    pub const fn new(x: T) -> Self {
        Self(x)
    }

    /// Constructs a new value of type `Padded<T, M>` containing a payload `x`,
    /// with an explicit generic argument for `M`.
    ///
    /// When the generic argument `M` can be inferred, it is recommended to
    /// use [`new`] instead.
    #[must_use]
    pub const fn with_padding<const M: usize>(x: T) -> Padded<T, M> {
        Padded(x)
    }

    /// Destructs a `Padded<T, N>` value and returns its payload
    #[must_use]
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Returns a reference to the payload value of a borrowed `Padded<T, N>`
    #[must_use]
    #[inline]
    pub const fn as_inner(&self) -> &T {
        &self.0
    }

    /// Returns a mutable reference to the payload value of a mutably borrowed `Padded<T, N>`
    #[must_use]
    #[inline]
    pub fn as_mut_inner(&mut self) -> &mut T {
        &mut self.0
    }

    /// Returns the number of bytes of padding for an arbitrary `Padded<T, N>` value.
    ///
    /// This is equal in value to [`PADDING`], but can be used when only a value is held,
    /// and its type is not in scope to qualify with.
    #[must_use]
    #[inline]
    pub const fn padding(&self) -> usize {
        N
    }
}

impl<T, const N: usize> From<T> for Padded<T, N> {
    fn from(val: T) -> Self {
        Self(val)
    }
}

impl<T: Encode, const N: usize> Encode for Padded<T, N> {
    /// Serializes the payload value of type `T`, followed by `N` null bytes
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf) + buf.push_many([0; N]) + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for Padded<T, N> {
    /// Parses a value of type `T` and consumes `N` subsequent bytes, returning the
    /// parsed value as `Padded<T, N>`.
    ///
    /// If both the initial parse and the subsequent `N`-byte consume operations
    /// succeed, this method will succeed by default; however when the
    /// `check_padding` feature-flag is enabled, this method will return an error
    /// value if any non-null values are found in the padding-bytes.
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        // FIXME: potential bug if parsing `T` consumes padding bytes
        let ret = T::parse(p)?;
        let _padding = p.consume(N)?;
        #[cfg(feature = "check_padding")]
        {
            if _padding != &[0u8; N] {
                let padding: Vec<u8> = _padding.to_vec();
                return Err(crate::parse::error::TokenError::NonNullPaddingByte { padding }.into());
            }
        }
        Ok(Self(ret))
    }
}

impl<T: Estimable, const N: usize> Estimable for Padded<T, N> {
    const KNOWN: Option<usize> = {
        match T::KNOWN {
            Some(m) => Some(m + N),
            None => {
                if cfg!(feature = "relaxed_padding_invariant") {
                    None
                } else {
                    unsafe { std::hint::unreachable_unchecked() }
                }
            }
        }
    };

    fn unknown(&self) -> usize {
        self.0.unknown() + N
    }
}

/// Optional value with no prefix
///
/// A newtype around `Option<T>` that is encoded without any discriminant:
/// A `None`-value is encoded as zero-width, and a `Some`-value is encoded
/// directly.
///
/// Aside from serialization and deserialization, this type is intended to
/// be behaviorally equivalent to `Option<T>`
///
/// Note that this type is semantically constrained to serve only as a
/// mechanism for optional fields in schemata, and as a return value, does
/// not indicate the availability of a result or the success/failure of
/// a fallible operation. In that respect,
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Nullable<T>(Option<T>);

impl<T> Nullable<T> {
    /// Returns `true` if the contained `Option<T>` is a [`Some`](std::option::Option::Some) value
    #[inline]
    #[must_use]
    pub const fn is_some(&self) -> bool {
        self.0.is_some()
    }

    /// Returns `true` if the contained `Option<T>` is a [`None`](std::option::Option::None) value
    #[inline]
    #[must_use]
    pub const fn is_none(&self) -> bool {
        self.0.is_none()
    }

    /// Destructs a `Nullable<T>` into the `Option<T>` it contains
    #[inline]
    pub fn into_inner(self) -> Option<T> {
        self.0
    }

    #[inline]
    #[must_use]
    /// Returns an immutable reference to the inner `Option<T>` in an immutably borrowed `Nullable<T>`
    pub fn as_inner(&self) -> &Option<T> {
        &self.0
    }

    #[inline]
    #[must_use]
    /// Returns a mutable reference to the inner `Option<T>` in a mutably borrowed `Nullable<T>`
    pub fn as_mut_inner(&mut self) -> &mut Option<T> {
        &mut self.0
    }
}

impl<T> Default for Nullable<T> {
    #[inline]
    fn default() -> Self {
        Self(None)
    }
}

impl<T> From<Nullable<T>> for Option<T> {
    fn from(val: Nullable<T>) -> Self {
        val.0
    }
}

impl<T> From<Option<T>> for Nullable<T> {
    fn from(val: Option<T>) -> Self {
        Self(val)
    }
}

impl<T> From<T> for Nullable<T> {
    fn from(val: T) -> Self {
        Self(Some(val))
    }
}

impl<T: Estimable> Estimable for Nullable<T> {
    const KNOWN: Option<usize> = {
        match T::KNOWN {
            // FIXME: ZSTs are not sensible in Nullable fields
            Some(0) => Some(0),
            _ => None,
        }
    };

    fn unknown(&self) -> usize {
        match self.0 {
            Some(ref x) => x.estimate(),
            None => 0,
        }
    }
}

impl<T: Encode> Encode for Nullable<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        match &self.0 {
            Some(x) => x.write_to(buf) + buf.resolve_zero(),
            None => buf.resolve_zero(),
        }
    }
}

impl<T: Decode> Decode for Nullable<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        if p.remainder() != 0 {
            Ok(Self(Some(T::parse(p)?)))
        } else {
            Ok(Self(None))
        }
    }
}

/// Opaque sequence of bytes
///
/// Newtype representing opaque, variable-length sequences of opaque bytes.
/// Similar to [`ByteString`](crate::fixed::ByteString::ByteString), which
/// represents constant-length binary sequences.
///
/// Although technically the operational semantics happen to coincide as currently
/// implemented, this type covers distinct cases from `Sequence<u8>`.
///
/// This type may occur in contexts where more descriptional schemas cannot be
/// used without incurring overhead or breaking backwards compatibility with
/// the schema layout defined in earlier protocol version.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct Bytes(Vec<u8>);

#[cfg(feature = "serde_impls")]
impl Serialize for Bytes {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
        serializer.serialize_bytes(&self.0)
    }
}


impl Bytes {
    /// Constructs a new, empty byte-sequence
    ///
    /// As with `Vec::new()`, no allocation is performed until bytes are added
    #[inline]
    #[must_use]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Constructs a `Bytes` value from a `Vec<u8>`
    pub const fn from_vec(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// Destructs a `Bytes` value and returns the actual `Vec<u8>` it contained
    ///
    /// The method name is chosen so as to avoid ambiguity with [`std::slice::to_vec`]
    /// arising from deref-coercion.
    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.0.as_slice()
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut_slice()
    }
}

impl IntoIterator for Bytes {
    type Item = u8;

    type IntoIter = std::vec::IntoIter<u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a> IntoIterator for &'a Bytes {
    type Item = &'a u8;

    type IntoIter = core::slice::Iter<'a, u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut Bytes {
    type Item = &'a mut u8;

    type IntoIter = core::slice::IterMut<'a, u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl std::iter::FromIterator<u8> for Bytes {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self(Vec::<u8>::from_iter(iter))
    }
}

impl Extend<u8> for Bytes {
    fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl From<Bytes> for Vec<u8> {
    #[inline]
    fn from(val: Bytes) -> Self {
        val.0
    }
}

impl From<Vec<u8>> for Bytes {
    #[inline]
    fn from(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }
}

impl<const N: usize> From<[u8; N]> for Bytes {
    #[inline]
    fn from(bytes: [u8; N]) -> Self {
        Self(bytes.to_vec())
    }
}

impl<const N: usize> From<&'_ [u8; N]> for Bytes {
    #[inline]
    fn from(bytes: &'_ [u8; N]) -> Self {
        Self(bytes.to_vec())
    }
}

impl<const N: usize> From<&'_ mut [u8; N]> for Bytes {
    #[inline]
    fn from(bytes: &'_ mut [u8; N]) -> Self {
        Self(bytes.to_vec())
    }
}

impl From<&'_ [u8]> for Bytes {
    #[inline]
    fn from(bytes: &'_ [u8]) -> Self {
        Self(bytes.to_vec())
    }
}

impl From<&'_ mut [u8]> for Bytes {
    #[inline]
    fn from(bytes: &'_ mut [u8]) -> Self {
        Self(bytes.to_vec())
    }
}

impl From<Box<[u8]>> for Bytes {
    #[inline]
    fn from(val: Box<[u8]>) -> Self {
        Self(val.into_vec())
    }
}

impl From<Bytes> for Box<[u8]> {
    fn from(bytes: Bytes) -> Self {
        bytes.0.into_boxed_slice()
    }
}

impl Encode for Bytes {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf)
    }

    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        self.0.write_to_vec(buf);
    }

    fn encode<U: Target>(&self) -> U {
        let mut tgt: U = U::create();
        self.0.write_to(&mut tgt);
        tgt
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }
}

impl Decode for Bytes {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(Self(p.take_dynamic(p.remainder())?))
    }
}

impl Estimable for Bytes {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.len()
    }

    fn estimate(&self) -> usize {
        self.0.len()
    }
}
