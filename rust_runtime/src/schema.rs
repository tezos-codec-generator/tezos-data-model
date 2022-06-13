use crate::conv::target::Target;
use crate::conv::{len, Decode, Encode};
use crate::error::ConstraintError;
use crate::parse::{ParseResult, Parser};
use crate::Estimable;
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::ops::DerefMut;
use std::{self, ops::Deref};

/// `Padded<T, N>`: Represents a value of type `T` with `N` trailing bytes of
/// padding.
///
/// It is expected, though not strictly mandatory, that all of the padding bytes
/// are zeroed out. The implmentation of Encode is guaranteed to use 0 for padding
/// but does not require that the padding be zeroed-out in the implementation of
/// Decode.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Default)]
pub struct Padded<T, const N: usize>(T);

impl<T, const N: usize> Padded<T, N> {
    pub const PADDING: usize = N;

    pub fn new(x: T) -> Self {
        Self(x)
    }

    pub fn with_padding<const M: usize>(x: T) -> Padded<T, M> {
        Padded(x)
    }

    pub fn into_inner(self) -> T {
        self.0
    }

    pub const fn as_inner(&self) -> &T {
        &self.0
    }

    pub fn as_mut_inner(&mut self) -> &mut T {
        &mut self.0
    }

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
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf) + buf.push_many([0; N]) + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for Padded<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let ret = T::parse(p)?;
        let _padding = p.consume(N)?;
        #[cfg(feature = "check_padding")]
        {
            if _padding != &[0u8; N] {

                return Err(crate::parse::error::TokenError::NonNullPaddingByte { padding: (), invalid: () })
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nullable<T>(Option<T>);

impl<T> Default for Nullable<T> {
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
            Some(0usize) => Some(0),
            _ => None,
        }
    };

    fn unknown(&self) -> usize {
        self.0.as_ref().map_or(0, <T as Estimable>::unknown)
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Bytes(Vec<u8>);

impl len::ScalarLength for Bytes {
    type Elem = u8;

    const PER_ELEM: usize = 1;

    fn n_elems(&self) -> usize {
        self.0.len()
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.deref_mut()
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

impl Encode for Bytes {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf)
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

pub mod boundedseq_impl {
    use crate::error::ConstraintError;

    pub trait IsBoundedSeq {
        type Elem;
        const LIMIT: usize;
    }

    pub trait BoundedSeqImpl
    where
        Self: IsBoundedSeq,
    {
        fn len(&self) -> usize;

        fn is_empty(&self) -> bool {
            self.len() == 0
        }

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
    ///
    /// This
    #[derive(Clone, Debug, Ord, Eq, PartialOrd, PartialEq, Hash)]
    pub struct FixSeq<T, const N: usize>(Vec<T>);

    impl<T, const N: usize> super::boundedseq_impl::IsBoundedSeq for FixSeq<T, N> {
        type Elem = T;

        const LIMIT: usize = N;
    }

    impl<T, const N: usize> super::boundedseq_impl::BoundedSeqImpl for FixSeq<T, N> {
        fn len(&self) -> usize {
            self.0.len()
        }

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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
#[cfg(feature = "arrayvec_fixseq")]
pub mod fixseq_arrayvec {
    use arrayvec::ArrayVec;

    #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct FixSeq<T, const N: usize>(ArrayVec<T, N>);

    impl<T, const N: usize> FixSeq<T, N> {
        pub unsafe fn push_unchecked(dest: &mut Self, value: T) {
            ArrayVec::push_unchecked(&mut dest.0, value)
        }

        pub fn try_push(dest: &mut Self, value: T) -> Result<(), ConstraintError> {
            if dest.len() < N {}
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
        let mut seq: FixSeq<T, N> = Default::default();

        while p.remainder() != 0 {
            boundedseq_impl::BoundedSeqImpl::try_push(&mut seq, T::parse(p)?)?;
        }

        Ok(seq)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct LimSeq<T, const N: usize>(Vec<T>);

impl<T, const N: usize> From<LimSeq<T, N>> for Vec<T> {
    fn from(val: LimSeq<T, N>) -> Self {
        val.0
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for LimSeq<T, N> {
    type Error = crate::error::ConstraintError;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        let l = value.len();
        if l <= N {
            Ok(Self(value))
        } else {
            Err(ConstraintError::TooManyElements {
                limit: N,
                actual: l,
            })
        }
    }
}

impl<T, const N: usize> Deref for LimSeq<T, N> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: len::Estimable, const N: usize> len::Estimable for LimSeq<T, N> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.iter().map(len::Estimable::estimate).sum()
    }
}

impl<T: Encode, const N: usize> Encode for LimSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.iter().map(|item| item.write_to(buf)).sum::<usize>() + buf.resolve_zero()
    }
}

impl<T: Decode, const N: usize> Decode for LimSeq<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Vec<T> = Vec::new();

        while p.remainder() != 0 {
            {
                let l = seq.len();
                if l >= N {
                    return Err(ConstraintError::TooManyElements {
                        limit: N,
                        actual: l,
                    }
                    .into());
                }
            }
            seq.push(T::parse(p)?);
        }

        Ok(seq.try_into()?)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
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
    pub fn from_vec(v: Vec<T>) -> Self {
        Self(v)
    }

    /// Destructs a `Sequence<T>` into its internal `Vec<T>`
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }

    ///
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.0.as_mut_slice()
    }
}


impl<T> std::default::Default for Sequence<T> {
    fn default() -> Self {
        Self(Default::default())
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
