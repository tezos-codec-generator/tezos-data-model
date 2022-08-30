//! Sequence-type with a fixed number of elements
//!
//! This module defines [`FixSeq<T, N>`], a schema-specific construct that
//! models sequences (as described in the super-module documentation) that holds
//! exactly `N` elements of type `T`.
//!
//! While it may be possible to construct, and manipulate, [`FixSeq<T, N>`]
//! values that are under-saturated, having fewer than `N` initialized elements,
//! some operations, in particular codec-related ones such as
//! [`Encode`](crate::conv::Encode) and [`Decode`](crate::conv::Decode) methods
//! will enforce a requirement that the length is exactly `N`.
//!
//! Over-saturated values cannot be constructed without violating implementation
//! boundaries, which may result in undefined behavior depending on internal
//! implementation details.

use cfg_if::cfg_if;

use crate::conv::{len::Estimable, target::Target, Decode, Encode};
use crate::error::LengthError;
use crate::parse::{error::ParseResult, Parser};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use super::boundedseq_impl::{BoundedSeqImpl, IsBoundedSeq};

mod inner {
    use cfg_if::cfg_if;

    cfg_if! {
        if #[cfg(feature = "arrayvec_fixseq")] {
            /// Utility alias to allow clean alternation between
            /// different implementations of [`FixSeq`](super::FixSeq)
            pub type Inner<T, const N: usize> = arrayvec::ArrayVec<T, N>;

            /// Consume an [`Inner<T, N>`] and return a `Vec<T>` with the same contents
            pub fn vectorize<T, const N: usize>(val: Inner<T, N>) -> Vec<T> {
                val.into_iter().collect::<Vec<T>>()
            }

            pub fn internalize<T, const N: usize>(val: Vec<T>) -> Inner<T, N> {
                val.into_iter().collect()
            }
        } else {
            /// Utility alias to allow clean alternation between
            /// different implementations of [`FixSeq`](super::FixSeq)
            pub type Inner<T, const N: usize> = Vec<T>;

            /// Consume an [`Inner<T, N>`] and return a `Vec<T>` with the same contents
            pub fn vectorize<T, const N: usize>(val: Inner<T, N>) -> Vec<T> {
                val
            }

            /// Consume a `Vec<T>` and return an [`Inner<T, N>`] with the same contents
            pub fn internalize<T, const N: usize>(val: Vec<T>) -> Inner<T, N> {
                val
            }
        }
    }
}

/// Sequence type holding exactly `N` elements of type `T`
///
/// This requirement of capacity-saturation is only enforced
/// at certain layers, such as serialization and deserialization
/// using [`Encode`] and [`Decode`] methods; otherwise, undersaturated
/// values may be constructed and manipulated so long as they are
/// either discarded, or become saturated before operations that enforce
/// this condition.
///
/// Certain trait methods, such as [`FromIterator::from_iter`]
/// and [`Extend::extend`], may panic when they would oversaturate
/// a `FixSeq<T, N>` value.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Hash)]
pub struct FixSeq<T, const N: usize>(inner::Inner<T, N>);

impl<T, const N: usize> FixSeq<T, N> {
    cfg_if! {
        if #[cfg(feature = "arrayvec_fixseq")] {
            /// Constructs a new, empty `FixSeq<T, N>`
            pub fn new() -> Self {
                Self(inner::Inner::<T, N>::new())
            }
        } else {
            /// Constructs a new, empty `FixSeq<T, N>`
            pub fn new() -> Self {
                Self(inner::Inner::<T, N>::with_capacity(N))
            }
        }
    }
}

impl<T, const N: usize> IsBoundedSeq for FixSeq<T, N> {
    type Elem = T;

    const LIMIT: usize = N;
}

impl<T, const N: usize> BoundedSeqImpl for FixSeq<T, N> {
    #[inline]
    unsafe fn push_unchecked(&mut self, value: T) {
        cfg_if! {
            if #[cfg(feature = "arrayvec_fixseq")] {
                self.0.push_unchecked(value)
            } else {
                self.0.push(value)
            }
        }
    }
}

impl<T, const N: usize> std::default::Default for FixSeq<T, N> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> From<FixSeq<T, N>> for Vec<T> {
    fn from(val: FixSeq<T, N>) -> Self {
        inner::vectorize::<T, N>(val.0)
    }
}

impl<T, const N: usize> IntoIterator for FixSeq<T, N> {
    type Item = T;

    type IntoIter = <inner::Inner<T, N> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a FixSeq<T, N> {
    type Item = &'a T;

    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

/// Extend the `FixSeq` with an iterator
///
/// ***Panics*** if the iterator would yield more elements than could fit into
/// the internal buffer without exceeding the length-limit.
impl<T, const N: usize> std::iter::Extend<T> for FixSeq<T, N> {
    /// Extends a `FixSeq` with the contents of an iterator
    ///
    /// # Panics
    ///
    /// This method will *panic* when the provided iterator yields more
    /// items than the remaining unused capacity of `self`
    ///
    /// Will also panic if `self` is already over-saturated, which
    /// is only possible when the `arrayvec_fixseq` feature is not enabled.
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let rem: usize = if cfg!(feature = "arrayvec_fixseq") {
            N - self.len()
        } else {
            N.checked_sub(self.len())
                .unwrap_or_else(|| panic!("cannot extend already-oversaturated FixSeq"))
        };
        let mut i = iter.into_iter();
        if i.by_ref().nth(rem).is_some() {
            panic!("attempted extend operation would overflow FixSeq capacity");
        }
        let max_iter = i.take(rem);
        self.0.extend(max_iter);
        debug_assert!(self.0.len() <= N);
    }
}

/// Create a `FixSeq` from an iterator
///
/// ***Panics*** if the number of elements in the iterator exceeds the `FixSeq`'s capacity
impl<T, const N: usize> FromIterator<T> for FixSeq<T, N> {
    /// Create a `FixSeq<T, N>` from an iterator
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the iterator exceeds the capacity `N`
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut i = iter.into_iter();
        if i.by_ref().nth(N).is_some() {
            panic!("attempted from_iter operation would overflow FixSeq capacity");
        }
        let max_iter = i.take(N);
        let ret = inner::Inner::from_iter(max_iter);
        debug_assert!(ret.len() <= N);
        Self(ret)
    }
}

impl<T, const N: usize> Deref for FixSeq<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl<T, const N: usize> DerefMut for FixSeq<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.deref_mut()
    }
}

impl<T, const N: usize> std::convert::TryFrom<&'_ [T]> for FixSeq<T, N>
where
    T: Clone,
{
    type Error = LengthError;

    /// Attempt to convert a slice into a `FixSeq<T, N>`.
    ///
    /// # Error
    ///
    /// Returns [`LengthError::TooLong`] if the slice contained more than
    /// `N` elements.
    ///
    /// Note that if the slice contained fewer than `N` elements, the conversion
    /// will not fail, despite the fact that the resulting `FixSeq<T, N>` will
    /// be undersaturated, and the deficit number of elements must be added
    /// before it is in a valid state for the purposes of encoding.
    fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
        if N != slice.len() {
            Err(LengthError::WrongLength {
                exact: N,
                actual: slice.len(),
            })
        } else {
            Ok(Self(inner::Inner::<T, N>::try_from(slice).unwrap()))
        }
    }
}

impl<T, const N: usize> std::convert::TryFrom<Vec<T>> for FixSeq<T, N> {
    type Error = LengthError;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        if N < value.len() {
            Err(LengthError::TooLong {
                limit: N,
                actual: value.len(),
            })
        } else {
            Ok(Self(inner::internalize::<T, N>(value)))
        }
    }
}

impl<T: Estimable, const N: usize> Estimable for FixSeq<T, N> {
    const KNOWN: Option<usize> = match <T as Estimable>::KNOWN {
        Some(m) => Some(N * m),
        None => None,
    };

    fn unknown(&self) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(Estimable::unknown)
            .sum()
    }
}

impl<T: Encode, const N: usize> Encode for FixSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for FixSeq<T, N>
where
    T: Decode,
{
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq = Self::new();

        // FIXME: loop should exit after N iterations even if bytes remain
        while p.remainder() != 0 {
            seq.try_push(T::parse(p)?)?;
        }

        if seq.len() == N {
            Ok(seq)
        } else {
            Err(crate::error::LengthError::WrongLength {
                exact: N,
                actual: seq.len(),
            }
            .into())
        }
    }
}
