//! Extension trait for Targets with monoidal concatenation
//!
//! This module is dedicated to the definition of the
//! `Builder` trait, a sub-trait of `Target, borrowing the name
//! from the ubiquitous Haskell package `bytestring` package.
//!
//! # Design
//!
//! A `Builder` is a kind of `Target` that can be optimized
//! for a potentially large number of build-up operations
//! (appending, concatenation, or `Target::push_*` methods)
//! with the aid of `AddAssign` and `Add` as supertrait
//! bounds, to allow monoid-like accumulation. Note that
//! it may be more efficient to avoid building up
//! multiple `Builders` and adding them, unless the specific
//! implementation is optimized for cheap concatenation.
//!
//! `Builder` types also implicitly include a `Final` type,
//! which freezes the contents of the `Builder`, and acts
//! as an intermediary between the write-only `Builder` type and
//! whatever end-point is intended for its contents to be
//! processed by or written to.
//!
//! # Layout
//!
//! This module contains the definition of the `Builder` trait
//! itself, as well as two submodules that implement `Builder`
//! types: `strict` for `StrictBuilder`, and `memo` for
//! `MemoBuilder`.
//!
//! It is possible that more implementing types will be added
//! in future, in which case they will be added to the above list.


use std::string::FromUtf8Error;
use crate::conv::target::Target;
use crate::util::hex_of_bytes;

/// `Target` extension trait with monoidal concatenation
///
/// Monoidal (through `std::ops::Add`) string-builder
/// made up of raw bytes, that can be displayed as a hexstring
/// or a raw binary string
///
/// In addition to various methods, defines two trait-level types,
/// `Segment` and `Final`.
///
/// The proper type to use for `Segment` depends entirely on the
/// nature of the implementing type. It is usually a primitive
/// or standard-library type that is a fractional part of the
/// `Builder` type in question, with cheap promotion into `Self`
/// via the `Builder::promote` method.
///
/// `Final` is also implementation-dependent, but at the very least
/// is required to implement `Into<Vec<u8>>`. Otherwise, it is intended
/// to be a read-oriented analogue of the write-optimized `Self`.
/// destination. Finalizing a `Builder` with the terminal operation
/// `finalize` will consume it and return a `Self::Final` value. This
/// value must contain the same bytes in the same traversal order, but
/// may have a completely different structural layout or metadata.
pub trait Builder
where
    Self: Target + Sized,
{
    /// Basic type of fractional components of a `Builder` object
    type Segment;

    /// Type suitable for presenting the finalized contents of a `Builder` object
    type Final: Into<Vec<u8>>;

    /// Converts a `Self::Segment` value into a `Self` value
    fn promote(seg: Self::Segment) -> Self;

    /// Creates a `Self` object containing a single byte
    fn word(b: u8) -> Self;

    /// Creates a `Self` object containing a fixed number of bytes
    fn words<const N: usize>(arr: [u8; N]) -> Self;

    /// Converts a `Self` value into a `Self::Final` value once
    /// it is fully built.
    fn finalize(self) -> Self::Final;

    /// Consume the Builder object and return a vector of its contents
    fn into_vec(self) -> Vec<u8> {
        self.finalize().into()
    }

    /// Return a string consisting of the raw hexadecimal sequence of words in the Builder
    fn into_hex(self) -> String {
        hex_of_bytes(self.into_vec())
    }

    /// Return a Builder object containing zero bytes. Defaults to words over empty array.
    fn empty() -> Self {
        Self::words([])
    }
    /// Attempt to convert the Builder object into a string in binary representation
    fn into_bin(self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.into_vec())
    }

    /// Determine the length of the Builder value in bytes
    fn len(&self) -> usize;

    /// Returns `true` if the receiver contains no bytes
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub mod memo;
pub mod strict;