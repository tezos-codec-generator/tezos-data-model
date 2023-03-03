//! Sequence-type with a limited number of elements
//!
//! This module defines [`LimSeq<T, N>`], a schema-specific construct that
//! models sequences (as described in the super-module documentation) that holds
//! no more than `N` elements of type `T`.
//!
//! Over-saturated values cannot be constructed without violating implementation
//! boundaries, which may result in undefined behavior depending on internal
//! implementation details.

use crate::conv::{len::Estimable, target::Target, Decode, Encode};
use crate::error::LengthError;
use crate::parse::{error::ParseResult, Parser};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use super::boundedseq_impl::{BoundedSeqImpl, IsBoundedSeq};

mod inner {
    /// Type-alias used throughout the definition of [`LimSeq`](super::LimSeq)
    /// instead of the actual type-name of the internal buffer-type, to allow
    /// multiple alternate implementations to be written concisely.
    ///
    /// When the `arrayvec_limseq` feature is set,
    /// this alias points to `arrayvec::ArrayVec<T, N>`
    ///
    /// Otherwise, it will default to `Vec<T>`
    #[cfg(feature = "arrayvec_limseq")]
    pub type Inner<T, const N: usize> = arrayvec::ArrayVec<T, N>;

    /// Type-alias used throughout the definition of [`LimSeq`](super::LimSeq)
    /// instead of the actual type-name of the internal buffer-type, to allow
    /// multiple alternate implementations to be written concisely.
    ///
    /// When the `arrayvec_limseq` feature is set,
    /// this alias points to `arrayvec::ArrayVec<T, N>`
    ///
    /// Otherwise, it will default to `Vec<T>`
    #[cfg(not(feature = "arrayvec_limseq"))]
    pub type Inner<T, const N: usize> = Vec<T>;




}

/// Sequence type holding at most `N` elements of type `T`
///
/// Certain trait methods, such as [`FromIterator::from_iter`]
/// and [`Extend::extend`], may panic when they would oversaturate
/// a `LimSeq<T, N>` value.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
pub struct LimSeq<T, const N: usize>(inner::Inner<T, N>);

impl<T, const N: usize> LimSeq<T, N> {
    /// Constructs a new, empty `LimSeq<T, N>`
    pub fn new() -> Self {
        Self::default()
    }

    /// Destruct a `FixSeq<T, N>` into a `Vec<T>` with the same contents
    ///
    /// Normally, this operation is a simple move,
    /// but when the `arrayvec_limseq` feature is enabled,
    /// this operation has additional overhead in converting
    /// out of `arrayvec::ArrayVec`.
    pub fn into_vec(self) -> Vec<T> {
        #[cfg(feature = "arrayvec_limseq")]
        {
            self.0.into_iter().collect()
        }
        #[cfg(not(feature = "arrayvec_limseq"))]
        {
            self.0
        }
    }

    /// Converts a `Vec<T>` into a `LimSeq<T, N>`
    /// with the same contents, without checking that the length of the vector
    /// is less than or equal to `N`.
    ///
    /// For a version of this function that performs this check, see
    /// [`from_vec`].
    ///
    /// # Panics
    ///
    /// This method will panic if the `arrayvec_limseq` feature is enabled
    /// and the length of `value` exceeds `N`.
    ///
    /// When `arrayvec_limseq` is not enabled, this method will not panic,
    /// but will instead return an oversaturated collection that will result
    /// in a panic when certain methods are called on it, most notably
    /// methods of the [`Encode`](crate::conv::Encode) trait.
    ///
    /// # Safety
    ///
    /// This method does not perform unsafe operations, but is marked
    /// as unsafe as it is intended only to be used when the length of
    /// `value` is known in advance to be less than or equal to `N`.
    pub unsafe fn from_vec_unchecked(value: Vec<T>) -> Self {
        #[cfg(feature = "arrayvec_limseq")]
        {
            Self(value.into_iter().collect())
        }
        #[cfg(not(feature = "arrayvec_limseq"))]
        {
            Self(value)
        }
    }

    /// Converts a `Vec<T>` into a `LimSeq<T, N>` with the same contents
    ///
    /// # Panics
    ///
    /// This method will panic if the length of `value` exceeds `N`
    pub fn from_vec(value: Vec<T>) -> Self {
        assert!(value.len() <= N, "cannot construct LimSeq from provided Vec without truncation");
        unsafe { Self::from_vec_unchecked(value) }
    }
}



impl<T, const N: usize> IsBoundedSeq for LimSeq<T, N> {
    type Elem = T;

    const LIMIT: usize = N;
}

impl<T, const N: usize> BoundedSeqImpl for LimSeq<T, N> {
    unsafe fn push_unchecked(&mut self, value: T) {
        #[cfg(not(feature = "arrayvec_limseq"))]
        {
            self.0.push(value)
        }
        #[cfg(feature = "arrayvec_limseq")]
        {
            self.0.push_unchecked(value)
        }
    }
}

impl<T, const N: usize> std::default::Default for LimSeq<T, N> {
    fn default() -> Self {
        #[cfg(not(feature = "arrayvec_limseq"))]
        {
            Self(inner::Inner::<T, N>::with_capacity(N))
        }
        #[cfg(feature = "arrayvec_limseq")]
        {
            Self(inner::Inner::<T, N>::new())
        }
    }
}

impl<T, const N: usize> From<LimSeq<T, N>> for Vec<T> {
    fn from(val: LimSeq<T, N>) -> Self {
        val.into_vec()
    }
}

impl<T, const N: usize> IntoIterator for LimSeq<T, N> {
    type Item = T;

    type IntoIter = <inner::Inner<T, N> as IntoIterator>::IntoIter;

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

/// Extend the `LimSeq` with an iterator
///
/// ***Panics*** if the iterator would yield more elements than could fit into
/// the internal buffer without exceeding the length-limit.
impl<T, const N: usize> std::iter::Extend<T> for LimSeq<T, N> {
    /// Extends a `LimSeq` with the contents of an iterator
    ///
    /// # Panics
    ///
    /// This method will *panic* when the provided iterator yields more
    /// items than the remaining unused capacity of `self`
    ///
    /// Will also panic if `self` is already over-saturated, which
    /// is only possible when the `arrayvec_limseq` feature is not enabled.
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let rem: usize = if cfg!(feature = "arrayvec_limseq") {
            N - self.len()
        } else {
            N.checked_sub(self.len())
                .unwrap_or_else(|| panic!("cannot extend already-oversaturated LimSeq"))
        };
        let mut i = iter.into_iter();
        if i.by_ref().nth(rem).is_some() {
            panic!("attempted extend operation would overflow LimSeq capacity");
        }
        let max_iter = i.take(rem);
        self.0.extend(max_iter);
        debug_assert!(self.0.len() <= N);
    }
}

/// Create a `LimSeq<T, N>` from an iterator
///
/// ***Panics*** if the number of elements in the iterator exceeds the `LimSeq`'s capacity
impl<T, const N: usize> FromIterator<T> for LimSeq<T, N> {
    /// Create a `LimSeq<T, N>` from an iterator
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the iterator exceeds the capacity `N`
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut i = iter.into_iter();
        if i.by_ref().nth(N).is_some() {
            panic!("attempted from_iter operation would overflow LimSeq capacity");
        }
        let max_iter = i.take(N);
        let ret = inner::Inner::<T, N>::from_iter(max_iter);
        debug_assert!(ret.len() <= N);
        Self(ret)
    }
}

impl<T, const N: usize> Deref for LimSeq<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl<T, const N: usize> DerefMut for LimSeq<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.deref_mut()
    }
}

impl<T, const N: usize> std::convert::TryFrom<&'_ [T]> for LimSeq<T, N>
where
    T: Clone,
{
    type Error = LengthError;

    fn try_from(slice: &[T]) -> Result<Self, Self::Error> {
        if N < slice.len() {
            Err(LengthError::TooLong {
                limit: N,
                actual: slice.len(),
            })
        } else {
            Ok(Self(inner::Inner::try_from(slice).unwrap()))
        }
    }
}

impl<T, const N: usize> std::convert::TryFrom<Vec<T>> for LimSeq<T, N> {
    type Error = LengthError;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        if N < value.len() {
            Err(LengthError::TooLong {
                limit: N,
                actual: value.len(),
            })
        } else {
            Ok(unsafe { Self::from_vec_unchecked(value) })
        }
    }
}

impl<T: Estimable, const N: usize> Estimable for LimSeq<T, N> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(Estimable::estimate)
            .sum()
    }
}

impl<T: Encode, const N: usize> Encode for LimSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T, const N: usize> Decode for LimSeq<T, N>
where
    T: Decode,
{
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq = Self::new();

        while p.remainder() != 0 {
            seq.try_push(T::parse(p)?)?;
        }

        Ok(seq)
    }
}
