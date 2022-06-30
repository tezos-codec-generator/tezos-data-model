use crate::error::LengthError;
use crate::parse::{Parser, error::ParseResult};
use crate::conv::{Decode, Encode, len::Estimable, target::Target};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use super::boundedseq_impl::{BoundedSeqImpl, IsBoundedSeq};

mod inner {
    #[cfg(feature = "arrayvec_limseq")]
    pub type Inner<T, const N: usize> = arrayvec::ArrayVec<T, N>;

    #[cfg(not(feature = "arrayvec_limseq"))]
    pub type Inner<T, const N: usize> = Vec<T>;

    #[cfg(feature = "arrayvec_limseq")]
    pub(crate) fn vectorize<T, const N: usize>(val: Inner<T, N>) -> Vec<T>
    where T: Clone {
        ::arrayvec::ArrayVec::as_slice(&val).to_vec()
    }

    #[cfg(not(feature = "arrayvec_limseq"))]
    pub(crate) fn vectorize<T, const N: usize>(val: Inner<T, N>) -> Vec<T>
    where T: Clone {
        val
    }

    #[cfg(feature = "arrayvec_limseq")]
    pub(crate) unsafe fn internalize<T, const N: usize>(mut value: Vec<T>) -> Inner<T, N> {
        value.drain(..).collect()
    }

    #[cfg(not(feature = "arrayvec_limseq"))]
    pub(crate) unsafe fn internalize<T, const N: usize>(value: Vec<T>) -> Inner<T, N> {
        value
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
#[cfg_attr(feature = "arrayvec_limseq", derive(Default))]
pub struct LimSeq<T, const N: usize>(inner::Inner<T, N>);

impl<T, const N: usize> IsBoundedSeq for LimSeq<T, N> {
    type Elem = T;

    const LIMIT: usize = N;
}

impl<T, const N: usize> super::boundedseq_impl::BoundedSeqImpl for LimSeq<T, N> {
    #[cfg(not(feature = "arrayvec_limseq"))]
    unsafe fn push_unchecked(&mut self, value: T) {
        Vec::<T>::push(&mut self.0, value)
    }

    #[cfg(feature = "arrayvec_limseq")]
    unsafe fn push_unchecked(&mut self, value: T) {
        ::arrayvec::ArrayVec::<T, N>::push_unchecked(&mut self.0, value)
    }
}

#[cfg(not(feature = "arrayvec_limseq"))]
impl<T, const N: usize> std::default::Default for LimSeq<T, N> {
    fn default() -> Self {
        Self(Vec::with_capacity(N))
    }
}

impl<T: Clone, const N: usize> From<LimSeq<T, N>> for Vec<T> {
    fn from(val: LimSeq<T, N>) -> Self {
        inner::vectorize::<T, N>(val.0)
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
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let rem: usize = N - self.len();
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
/// ***Panics*** if the number of elements in the iterator exceeds the LimSeq's capacity
impl<T, const N: usize> FromIterator<T> for LimSeq<T, N> {
    /// Create a `LimSeq<T, N>` from an iterator
    ///
    /// # Panics
    ///
    /// Panics if the number of elements in the iterator exceeds the LimSeq's capacity.
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
            Ok(Self(unsafe { inner::internalize::<T, N>(value) }))
        }
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

impl<T: Estimable, const N: usize> Estimable for LimSeq<T, N> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        <Self as Deref>::deref(self)
            .iter()
            .map(Estimable::unknown)
            .sum()
    }
}

impl<T: Encode, const N: usize> Encode for LimSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for LimSeq<T, N>
where
    Self: std::default::Default,
{
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Self = <LimSeq<T, N> as Default>::default();

        while p.remainder() != 0 {
            BoundedSeqImpl::try_push(&mut seq, T::parse(p)?)?;
        }

        Ok(seq)
    }
}
