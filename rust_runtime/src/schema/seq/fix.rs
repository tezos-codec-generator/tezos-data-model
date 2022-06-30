use crate::parse::error::ParseResult;
use crate::{Estimable, Encode, Target, Decode, Parser};
use crate::error::LengthError;
use crate::schema::seq::boundedseq_impl::{BoundedSeqImpl, IsBoundedSeq};
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

mod inner {
    #[cfg(feature = "arrayvec_fixseq")]
    pub type Inner<T, const N: usize> = arrayvec::ArrayVec<T, N>;

    #[cfg(not(feature = "arrayvec_fixseq"))]
    pub type Inner<T, const N: usize> = Vec<T>;

    #[cfg(feature = "arrayvec_fixseq")]
    pub(crate) fn vectorize<T: Clone, const N: usize>(val: Inner<T, N>) -> Vec<T> {
        ::arrayvec::ArrayVec::as_slice(&val).to_vec()
    }

    #[cfg(not(feature = "arrayvec_fixseq"))]
    pub(crate) fn vectorize<T: Clone, const N: usize>(val: Inner<T, N>) -> Vec<T> {
        val
    }
}

/// Sequence type with a type-level constant length
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Hash)]
#[cfg_attr(feature = "arrayvec_fixseq", derive(Default))]
pub struct FixSeq<T, const N: usize>(inner::Inner<T, N>);

impl<T, const N: usize> IsBoundedSeq for FixSeq<T, N> {
    type Elem = T;

    const LIMIT: usize = N;
}

impl<T, const N: usize> BoundedSeqImpl for FixSeq<T, N> {
    #[cfg(not(feature = "arrayvec_fixseq"))]
    unsafe fn push_unchecked(&mut self, value: T) {
        Vec::<T>::push(&mut self.0, value)
    }

    #[cfg(feature = "arrayvec_fixseq")]
    unsafe fn push_unchecked(&mut self, value: T) {
        ::arrayvec::ArrayVec::<T, N>::push_unchecked(&mut self.0, value)
    }
}

#[cfg(not(feature = "arrayvec_fixseq"))]
impl<T, const N: usize> std::default::Default for FixSeq<T, N> {
    fn default() -> Self {
        Self(Vec::with_capacity(N))
    }
}

impl<T: Clone, const N: usize> From<FixSeq<T, N>> for Vec<T> {
    fn from(val: FixSeq<T, N>) -> Self {
        inner::vectorize::<T, N>(val.0)
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
            panic!("attempted extend operation would overflow FixSeq capacity");
        }
        let max_iter = i.take(rem);
        self.0.extend(max_iter);
        debug_assert!(self.0.len() <= N);
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

impl<T, const N: usize> std::ops::Deref for FixSeq<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl<T, const N: usize> DerefMut for FixSeq<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        <inner::Inner<T, N> as DerefMut>::deref_mut(&mut self.0)
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
            super::boundedseq_impl::BoundedSeqImpl::try_push(&mut seq, T::parse(p)?)?;
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
