//! Specialized schema types
//!
//! Most types used in the `data-encoding` protocol can be defined
//! using native Rust equivalents, but several are specialized enough
//! to have no direct natural analogue.
//!
//! This module contains an assortment of such type definitions, including
//! the standard conversion methods that apply to the construct they model.
//!
//! Such types include:
//!  - Wrappers around types that add a fixed amount of NIL-byte padding
//!    ([`Padded<T, N>`])
//!  - Dynamic byte-sequences (`Bytes`)
//!  - Sequence types:
//!     - Variable-length: [`Sequence<T>`]
//!     - Bounded-length: [`LimSeq<T>`]
//!     - Constant-length: [`FixSeq<T>`]
//!  - Unprefixed optional values: [`Nullable<T>`]
//!
//! The organization of these types, and assorted schema-specific types
//! currently defined in separate modules, may be subject to change as the
//! library evolves.

use crate::conv::target::Target;
use crate::conv::{len, Decode, Encode};
use crate::parse::{ParseResult, Parser};
use crate::Estimable;
use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::DerefMut;
use std::{self, ops::Deref};

/// Schema-specific construct that simulates a value with `N` bytes of post-padding
///
/// A direct analogue to the `Padded` constructor in the `data-encoding` library
/// binary-schema AST.
///
/// A value of type `Padded<T, N>` is nothing more than a shallow wrapper around
/// a value of type `T`, but adheres to a model of serialization and deserialization
/// that appends, and correspondingly consumes, `N` extra bytes of padding, which
/// are assumed to be `NIL`-valued.
///
/// In `data-encoding` itself, the actual value of the padding-bytes during deserialization
/// is not enforced, but this can be thought of as more of an optimization around
/// the expected case, rather than as license for non-NIL bytes to be written
/// during serialization. Correspondingly, the default behavior in this library is to
/// likewise suppress post-validation of the padding, assuming that it can actually
/// be consumed legally.
///
/// This behavior can be controlled by setting the feature-flag `check_padding`,
/// which is typically unset. Doing so will incur a slight performance overhead
/// during the decoding of `Padded<T, N>` values, but will cause a novel error
/// category to be returned whenever a non-null byte is found among the
/// padding bytes.
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
        let ret = T::parse(p)?;
        let _padding = p.consume(N)?;
        #[cfg(feature = "check_padding")]
        {
            if _padding != &[0u8; N] {
                return Err(crate::parse::error::TokenError::NonNullPaddingByte {
                    padding: (),
                    invalid: (),
                });
            }
        }
        Ok(Self(ret))
    }
}

impl<T: len::Estimable, const N: usize> len::Estimable for Padded<T, N> {
    const KNOWN: Option<usize> = {
        match T::KNOWN {
            Some(m) => Some(m + N),
            None => None,
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
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub fn into_inner(self) -> Option<T> {
        self.0
    }

    /// Returns the contained [`Some`](std::option::Option::Some) value, consuming the `self` value.
    ///
    /// # Panics
    ///
    /// This function follows the same operational semantics as [`Option::unwrap`](std::option::Option::unwrap),
    /// which it is defined in terms of.
    pub fn unwrap(self) -> T {
        self.0.unwrap()
    }

    /// Returns the contained [`Some`] value or a provided default.
    ///
    /// As with [`Option::unwrap_or`](std::option::Option::unwrap_or), arguments to
    /// the function are eagerly evaluated.
    pub fn unwrap_or(self, default: T) -> T {
        self.0.unwrap_or(default)
    }

    /// Returns the contained [`Some`](std::option::Option::Some) value within
    /// the payload, or the default value of the type in question.
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        self.0.unwrap_or_default()
    }

    /// Returns the contained [`Some`](std::option::Option::Some) value within
    /// the payload, or computes it from a function.
    pub fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        self.0.unwrap_or_else(f)
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

impl<T> Debug for Nullable<T>
where
    Option<T>: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Option<T> as Debug>::fmt(&self.0, f)
    }
}

impl<T: Estimable> Estimable for Nullable<T> {
    const KNOWN: Option<usize> = {
        match T::KNOWN {
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
        self.write_to(buf);
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

impl len::Estimable for Bytes {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.len()
    }

    fn estimate(&self) -> usize {
        self.0.len()
    }
}

pub mod boundedseq_impl {
    use crate::error::ConstraintError;

    /// Marker trait for types suitable as implementations for `LimSeq` and `FixSeq`
    pub trait IsBoundedSeq {
        type Elem;
        const LIMIT: usize;
    }

    /// Extension trait for implementations of `LimSeq` and `FixSeq`
    pub trait BoundedSeqImpl
    where
        Self: IsBoundedSeq + std::ops::Deref<Target = [<Self as IsBoundedSeq>::Elem]>,
    {
        /// Pushes an element to the end of the bounded sequence without checking
        /// whether it violates the bounds of the type in question.
        ///
        /// # Safety
        ///
        /// This function is unsafe because it may be used to call the explicitly
        /// unsafe `arrayvec::ArrayVec::push_unchecked` method, which performs
        /// pointer operations that may cause Undefined Behavior if the bounds
        /// are violated.
        ///
        /// Beyond this, this method can append elements beyond the limit of the
        /// type in question, which is subject to panics later on, if an attempt
        /// is made to encode the oversaturated sequence in question.
        unsafe fn push_unchecked(&mut self, value: Self::Elem);

        fn try_push(&mut self, value: Self::Elem) -> Result<(), ConstraintError> {
            if self.len() < Self::LIMIT {
                unsafe {
                    self.push_unchecked(value);
                }
                Ok(())
            } else {
                Err(ConstraintError::TooManyElements {
                    limit: Self::LIMIT,
                    actual: Self::LIMIT + 1,
                })
            }
        }
    }
}

#[cfg_attr(feature = "arrayvec_fixseq", allow(dead_code))]
mod fixseq_vec {
    use std::iter::FromIterator;

    /// Sequence type with a type-level constant length
    #[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq, Hash)]
    pub struct FixSeq<T, const N: usize>(Vec<T>);

    impl<T, const N: usize> super::boundedseq_impl::IsBoundedSeq for FixSeq<T, N> {
        type Elem = T;

        const LIMIT: usize = N;
    }

    impl<T, const N: usize> super::boundedseq_impl::BoundedSeqImpl for FixSeq<T, N> {
        unsafe fn push_unchecked(&mut self, value: Self::Elem) {
            self.0.push(value)
        }
    }

    impl<T, const N: usize> std::default::Default for FixSeq<T, N> {
        fn default() -> Self {
            Self(Vec::with_capacity(N))
        }
    }

    impl<T, const N: usize> From<FixSeq<T, N>> for Vec<T> {
        fn from(val: FixSeq<T, N>) -> Self {
            val.0
        }
    }

    impl<T, const N: usize> IntoIterator for FixSeq<T, N> {
        type Item = T;

        type IntoIter = std::vec::IntoIter<T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl<'a, T: 'a, const N: usize> IntoIterator for &'a FixSeq<T, N> {
        type Item = &'a T;

        type IntoIter = core::slice::Iter<'a, T>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.iter()
        }
    }

    impl<T, const N: usize> FromIterator<T> for FixSeq<T, N> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            let mut fix_seq = Self::default();
            fix_seq.extend(iter);
            fix_seq
        }
    }

    impl<T, const N: usize> std::convert::TryFrom<&'_ [T]> for FixSeq<T, N>
    where
        T: Clone,
    {
        type Error = crate::error::ConstraintError;

        fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
            if N != slice.len() {
                Err(crate::error::ConstraintError::ConstantLengthViolation {
                    expected: N,
                    actual: slice.len(),
                })
            } else {
                Ok(Self(Vec::from(slice)))
            }
        }
    }

    impl<T, const N: usize> std::ops::Deref for FixSeq<T, N> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            self.0.deref()
        }
    }

    /// Extend the `FixSeq` with an iterator
    ///
    /// ***Panics*** if extending the internal vector exceeds its implicit capacity
    impl<T, const N: usize> std::iter::Extend<T> for FixSeq<T, N> {
        fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
            let rem: usize = N - self.len();
            let mut i = iter.into_iter();
            if i.by_ref().nth(rem).is_some() {
                panic!("attempted extend operation that would overflow FixSeq capacity");
            }
            let max_iter = i.take(rem);
            self.0.extend(max_iter);
            debug_assert!(self.0.len() <= N);
        }
    }
}

#[cfg(feature = "arrayvec_fixseq")]
pub mod fixseq_arrayvec {
    use arrayvec::ArrayVec;

    /// Sequence type with a type-level constant length
    #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FixSeq<T, const N: usize>(ArrayVec<T, N>);

    impl<T, const N: usize> FixSeq<T, N> {
        pub unsafe fn push_unchecked(dest: &mut Self, value: T) {
            ArrayVec::push_unchecked(&mut dest.0, value)
        }
    }

    impl<T, const N: usize> Deref for FixSeq<T, N> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            <ArrayVec<T, N> as Deref>::deref(&self.0)
        }
    }

    impl<T, const N: usize> DerefMut for FixSeq<T, N> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            <ArrayVec<T, N> as DerefMut>::deref_mut(&mut self.0)
        }
    }

    /// Extend the `FixSeq` with an iterator
    ///
    /// ***Panics*** if extending the internal vector exceeds its implicit capacity
    impl<T, const N: usize> Extend<T> for FixSeq<T, N> {
        /// Extend the `FixSeq` with an iterator
        ///
        /// # Panics
        ///
        /// ***Panics*** if extending the internal vector exceeds its implicit capacity
        fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
            self.0.extend(iter)
        }
    }

    /// Create a `FixSeq` from an iterator
    ///
    /// ***Panics*** if the number of elements in the iterator exceeds the FixSeq's capacity
    impl<T, const N: usize> FromIterator<T> for FixSeq<T, N> {
        /// Create a `FixSeq` from an iterator
        ///
        /// # Panics
        ///
        /// Panics if the number of elements in the iterator exceeds the FixSeq's capacity.
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            Self(<ArrayVec<T, N> as FromIterator<T>>::from_iter(iter))
        }
    }
}

#[cfg(feature = "arrayvec_fixseq")]
pub use fixseq_arrayvec::FixSeq;
#[cfg(not(feature = "arrayvec_fixseq"))]
pub use fixseq_vec::FixSeq;

impl<T: crate::Estimable, const N: usize> crate::Estimable for FixSeq<T, N> {
    const KNOWN: Option<usize> = match <T as crate::Estimable>::KNOWN {
        Some(m) => Some(N * m),
        None => None,
    };

    fn unknown(&self) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(len::Estimable::unknown)
            .sum()
    }
}

impl<T: Encode, const N: usize> Encode for FixSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(|item| item.write_to(buf))
            .sum::<usize>()
            + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for FixSeq<T, N>
where
    T: Decode,
    FixSeq<T, N>: std::default::Default + Extend<T>,
{
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Self = Default::default();

        while p.remainder() != 0 {
            boundedseq_impl::BoundedSeqImpl::try_push(&mut seq, T::parse(p)?)?;
        }

        if seq.len() == N {
            Ok(seq)
        } else {
            Err(crate::error::ConstraintError::ConstantLengthViolation {
                expected: N,
                actual: seq.len(),
            }
            .into())
        }
    }
}

#[cfg_attr(feature = "arrayvec_limseq", allow(dead_code))]
pub mod limseq_vec {
    use std::iter::FromIterator;
    /// Sequence type with a constant upper bound on length
    #[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq, Hash)]
    pub struct LimSeq<T, const N: usize>(Vec<T>);

    impl<T, const N: usize> super::boundedseq_impl::IsBoundedSeq for LimSeq<T, N> {
        type Elem = T;

        const LIMIT: usize = N;
    }

    impl<T, const N: usize> super::boundedseq_impl::BoundedSeqImpl for LimSeq<T, N> {
        unsafe fn push_unchecked(&mut self, value: Self::Elem) {
            self.0.push(value)
        }
    }

    impl<T, const N: usize> std::default::Default for LimSeq<T, N> {
        fn default() -> Self {
            Self(Vec::with_capacity(N))
        }
    }

    impl<T, const N: usize> From<LimSeq<T, N>> for Vec<T> {
        fn from(val: LimSeq<T, N>) -> Self {
            val.0
        }
    }

    impl<T, const N: usize> IntoIterator for LimSeq<T, N> {
        type Item = T;

        type IntoIter = std::vec::IntoIter<T>;

        #[inline]
        fn into_iter(self) -> Self::IntoIter {
            self.0.into_iter()
        }
    }

    impl<'a, T: 'a, const N: usize> IntoIterator for &'a LimSeq<T, N> {
        type Item = &'a T;

        type IntoIter = core::slice::Iter<'a, T>;

        fn into_iter(self) -> Self::IntoIter {
            self.0.iter()
        }
    }

    impl<T, const N: usize> FromIterator<T> for LimSeq<T, N> {
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            let mut seq = Self::default();
            seq.extend(iter);
            seq
        }
    }

    impl<T, const N: usize> std::convert::TryFrom<&'_ [T]> for LimSeq<T, N>
    where
        T: Clone,
    {
        type Error = crate::error::ConstraintError;

        fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
            if N < slice.len() {
                Err(crate::error::ConstraintError::TooManyElements {
                    limit: N,
                    actual: slice.len(),
                })
            } else {
                Ok(Self(Vec::from(slice)))
            }
        }
    }

    impl<T, const N: usize> std::convert::TryFrom<Vec<T>> for LimSeq<T, N> {
        type Error = crate::error::ConstraintError;

        fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
            if N < value.len() {
                Err(crate::error::ConstraintError::TooManyElements {
                    limit: N,
                    actual: value.len(),
                })
            } else {
                Ok(Self(value))
            }
        }
    }

    impl<T, const N: usize> std::ops::Deref for LimSeq<T, N> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            self.0.as_slice()
        }
    }

    /// Extend the `LimSeq` with an iterator
    ///
    /// ***Panics*** if extending the internal vector exceeds its implicit capacity
    impl<T, const N: usize> std::iter::Extend<T> for LimSeq<T, N> {
        fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
            let rem: usize = N - self.len();
            let mut i = iter.into_iter();
            if i.by_ref().nth(rem).is_some() {
                panic!("attempted extend operation that would overflow FixSeq capacity");
            }
            let max_iter = i.take(rem);
            self.0.extend(max_iter);
            debug_assert!(self.0.len() <= N);
        }
    }
}

#[cfg(feature = "arrayvec_limseq")]
pub mod limseq_arrayvec {
    use arrayvec::ArrayVec;

    /// Sequence type with a constant upper bound on length
    #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct LimSeq<T, const N: usize>(ArrayVec<T, N>);

    impl<T, const N: usize> LimSeq<T, N> {
        pub unsafe fn push_unchecked(dest: &mut Self, value: T) {
            ArrayVec::push_unchecked(&mut dest.0, value)
        }
    }

    impl<T, const N: usize> Deref for LimSeq<T, N> {
        type Target = [T];

        fn deref(&self) -> &Self::Target {
            <ArrayVec<T, N> as Deref>::deref(&self.0)
        }
    }

    impl<T, const N: usize> DerefMut for LimSeq<T, N> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            <ArrayVec<T, N> as DerefMut>::deref_mut(&mut self.0)
        }
    }

    /// Extend the `FixSeq` with an iterator
    ///
    /// ***Panics*** if extending the internal vector exceeds its implicit capacity
    impl<T, const N: usize> Extend<T> for LimSeq<T, N> {
        /// Extend the `FixSeq` with an iterator
        ///
        /// # Panics
        ///
        /// ***Panics*** if extending the internal vector exceeds its implicit capacity
        fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
            self.0.extend(iter)
        }
    }

    /// Create a `FixSeq` from an iterator
    ///
    /// ***Panics*** if the number of elements in the iterator exceeds the FixSeq's capacity
    impl<T, const N: usize> FromIterator<T> for LimSeq<T, N> {
        /// Create a `FixSeq` from an iterator
        ///
        /// # Panics
        ///
        /// Panics if the number of elements in the iterator exceeds the FixSeq's capacity.
        fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
            Self(<ArrayVec<T, N> as FromIterator<T>>::from_iter(iter))
        }
    }
}

#[cfg(feature = "arrayvec_limseq")]
pub use limseq_arrayvec::LimSeq;
#[cfg(not(feature = "arrayvec_limseq"))]
pub use limseq_vec::LimSeq;

impl<T: crate::Estimable, const N: usize> crate::Estimable for LimSeq<T, N> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(len::Estimable::unknown)
            .sum()
    }
}

impl<T: Encode, const N: usize> Encode for LimSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for LimSeq<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Self = Default::default();

        while p.remainder() != 0 {
            boundedseq_impl::BoundedSeqImpl::try_push(&mut seq, T::parse(p)?)?;
        }

        Ok(seq)
    }
}

/// Sequence type with unbounded variable length
///
/// `Sequence<T>` is modelled to use an underlying `Vec<T>`, but is only to be
/// used as unbounded-sequence codec elements.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[repr(transparent)]
pub struct Sequence<T>(Vec<T>);

impl<T> Sequence<T> {
    /// Constructs a new, empty sequence
    ///
    /// Initially contains no elements, and will not allocate until
    /// elements are added
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Converts an existing `Vec<T>` into a `Sequence<T>`
    #[must_use]
    pub fn from_vec(v: Vec<T>) -> Self {
        Self(v)
    }

    /// Destructs a `Sequence<T>` into its internal `Vec<T>`
    #[must_use]
    pub fn into_inner(self) -> Vec<T> {
        self.0
    }

    /// Returns a slice consisting of the full `Sequence<T>`
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }

    /// Returns a mutable slice consisting of the full `Sequence<T>`
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
}

impl<T> std::default::Default for Sequence<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> AsRef<[T]> for Sequence<T> {
    fn as_ref(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T> AsMut<[T]> for Sequence<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
}

#[cfg(feature = "deref_sequence")]
impl<T> Deref for Sequence<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0.as_slice()
    }
}

#[cfg(feature = "deref_sequence")]
impl<T> DerefMut for Sequence<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.as_mut_slice()
    }
}

impl<T> IntoIterator for Sequence<T> {
    type Item = T;

    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Sequence<T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Sequence<T> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T> FromIterator<T> for Sequence<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl<T> Extend<T> for Sequence<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<T> From<Sequence<T>> for Vec<T> {
    fn from(val: Sequence<T>) -> Self {
        val.0
    }
}

impl<T> From<Vec<T>> for Sequence<T> {
    fn from(seq: Vec<T>) -> Self {
        Self(seq)
    }
}

impl<T: len::Estimable> len::Estimable for Sequence<T> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.iter().map(len::Estimable::estimate).sum()
    }
}

impl<T: Encode> Encode for Sequence<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T: Decode> Decode for Sequence<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Vec<T> = Vec::new();

        while p.remainder() != 0 {
            seq.push(T::parse(p)?);
        }

        Ok(Self(seq))
    }
}
