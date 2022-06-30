//! Schema-level sequence types
//!
//! This module serves as an entry-point for the set of *sequence-types* defined
//! in this crate, which serve as analogues for the list- and array-based schema
//! components defined in `data-encoding`.
//!
//! # Sequences in `data-encoding`
//!
//! The schema language of `data-encoding` contains combinators for encoding
//! collections of values, either as an OCaml `list` or `array`.  Furthermore,
//! each of these cases allows for specification of a `length_limit`, which, in
//! the version of `data-encoding` this project is based on, is one of the
//! following:
//!     * `No_limit`
//!     * `At_most N`
//!     * `Exactly N`
//!
//! where `N` is some (non-negative) integer.
//!
//! `No_limit` corresponds to arrays, or lists, which have no locally-enforced
//! limit on the number of elements they contain (the number of bytes required
//! to encode such elements, however, may be either implicitly or explicitly
//! enforced by the context surrounding said element).
//!
//! `At_most N` corresponds to arrays and lists which are mandated to contain no
//! more than `N` elements, not necessarily at every stage of their construction
//! or modification, but certainly at the time an attempt is made to encode such
//! values. Similarly, `Exactly N` enforces a similar limit, with the added
//! restriction that the number of elements must equal `N`.
//!
//! The distinction between `array` and `list` is opaque at the encoding-level,
//! and only exists to determine which of `list` and `array` are expected in a
//! given position when encoding, and correspondingly which of the two is
//! produced in the same position when decoding. In light of this, the
//! distinction between `array`- and `list`-based schema elements is erased. The
//! only aspect of variation that is preserved is the length-limit.
//!
//! # `Sequence<T>`
//!
//! This module directly defines the type `Sequence<T>`, which is analogous to
//! both `list` and `array` schemas with a length-limit of `No_limit`; that is,
//! sequences of variable, unbounded length.
//!
//! In turn, the sub-module `fix` defines `FixSeq<T, N>`, which models sequences
//! with length-limits of `Exactly N`, of constant element-count but potentially
//! variable binary length; similarly, `lim` defines `LimSeq<T, N>` for `At_most
//! N`, for sequences with a bounded number of elements that are otherwise
//! variable in length.

use crate::conv::{len::Estimable, target::Target, Decode, Encode};
use crate::parse::{ParseResult, Parser};

use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::Index;

pub(crate) mod boundedseq_impl;

pub mod fix;
pub mod lim;

/// Ordered sequence containing an unbounded number of elements
///
/// # Sequences in `data-encoding`
///
/// `Sequence<T>` is used for both the `array` and `list` combinators in
/// `data-encoding`.
///
/// Specifically, an `Encoding.desc` element of the following form
/// `Array { length_limit = No_limit; _ }`
/// or `List { length_limit = No_limit; _ }`
///
/// `Sequence<T>` is modelled to use an underlying `Vec<T>`, but is only to be
/// used as unbounded-sequence codec elements.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(transparent)]
pub struct Sequence<T>(Vec<T>);

impl<T> Sequence<T> {
    /// Constructs a new, empty `Sequence`
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
    #[inline]
    pub fn from_vec(v: Vec<T>) -> Self {
        Self(v)
    }

    /// Destructs a `Sequence<T>` into the contained `Vec<T>`
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

impl<T, I> Index<I> for Sequence<T>
where
    I: std::slice::SliceIndex<[T]>
{
    type Output = <I as std::slice::SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        <Vec<T> as Index<I>>::index(&self.0, index)
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

impl<T> std::ops::Deref for Sequence<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.0.as_slice()
    }
}

impl<T> std::ops::DerefMut for Sequence<T> {
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

impl<T: Estimable> Estimable for Sequence<T> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.iter().map(Estimable::estimate).sum()
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

#[macro_export]
macro_rules! seq {
    () => { $crate::schema::seq::Sequence::new() };
    ($elem:expr; $n:expr) => { $crate::schema::seq::Sequence::from_vec(vec![$elem; $n]) };
    ($($x:expr),+ $(,)?) => { $crate::schema::seq::Sequence::from_vec(vec![$($x),*]) };
}