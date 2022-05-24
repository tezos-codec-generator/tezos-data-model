use crate::Estimable;
use crate::conv::target::Target;
use crate::conv::{len, Decode, Encode};
use crate::error::ConstraintError;
use crate::parse::{ParseResult, Parser};
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Padded<T, const N: usize>(T);

impl<T, const N: usize> Deref for Padded<T, N> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Encode, const N: usize> Encode for Padded<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.write_to(buf) + buf.push_many([0; N]) + crate::resolve_zero(buf)
    }
}

impl<T: Decode, const N: usize> Decode for Padded<T, N> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized,
    {
        let ret = T::parse(p)?;
        let _ = p.consume(N)?;
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Nullable<T>(Option<T>);

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

impl<T: Debug> Debug for Nullable<T> {
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
            Some(x) => x.write_to(buf) + crate::resolve_zero(buf),
            None => crate::resolve_zero(buf),
        }
    }
}

impl<T: Decode> Decode for Nullable<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where Self: Sized {
        if p.remainder() != 0 {
            Ok(T::parse(p)?.into())
        } else {
            Ok(None.into())
        }
    }
}


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Bytes(Vec<u8>);

impl len::ScalarLength for Bytes {
    type Elem = u8;

    const PER_ELEM: usize = 1;

    fn n_elems(&self) -> usize {
        self.0.len()
    }
}

impl Deref for Bytes {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<Bytes> for Vec<u8> {
    fn from(val: Bytes) -> Self {
        val.0
    }
}

impl From<Vec<u8>> for Bytes {
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
        Ok(Self(Vec::<u8>::parse(p)?))
    }
}

// TODO: should this be implemented as an array rather than a vector?
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct FixSeq<T, const N: usize>(Vec<T>);

impl<T, const N: usize> Into<Vec<T>> for FixSeq<T, N> {
    fn into(self) -> Vec<T> {
        self.0
    }
}

impl<T, const N: usize> TryFrom<Vec<T>> for FixSeq<T, N> {
    type Error = crate::error::ConstraintError;

    fn try_from(value: Vec<T>) -> Result<Self, Self::Error> {
        let l = value.len();
        if l == N {
            Ok(Self(value))
        } else {
            Err(ConstraintError::InexactCardinality {
                expected: N,
                actual: l,
            })
        }
    }
}

impl<T, const N: usize> Deref for FixSeq<T, N> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: len::Estimable, const N: usize> len::Estimable for FixSeq<T, N> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.iter().map(len::Estimable::estimate).sum()
    }
}

impl<T: Encode, const N: usize> Encode for FixSeq<T, N> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        self.0.iter().map(|item| item.write_to(buf)).sum::<usize>() + crate::resolve_zero(buf)
    }
}

impl<T: Decode, const N: usize> Decode for FixSeq<T, N> {
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
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct LimSeq<T, const N: usize>(Vec<T>);

impl<T, const N: usize> Into<Vec<T>> for LimSeq<T, N> {
    fn into(self) -> Vec<T> {
        self.0
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
        self.0.iter().map(|item| item.write_to(buf)).sum::<usize>() + crate::resolve_zero(buf)
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Sequence<T>(Vec<T>);

impl<T> Into<Vec<T>> for Sequence<T> {
    fn into(self) -> Vec<T> {
        self.0
    }
}

impl<T> From<Vec<T>> for Sequence<T> {
    fn from(seq: Vec<T>) -> Self {
        Self(seq)
    }
}

impl<T> Deref for Sequence<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Sequence<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
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
        self.0.iter().map(|item| item.write_to(buf)).sum::<usize>() + crate::resolve_zero(buf)
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
