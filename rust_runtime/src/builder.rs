use std::{borrow::Borrow, string::FromUtf8Error};

use crate::conv::target::Target;
use crate::util::hex_of_bytes;
use std::ops::{Add, AddAssign};

/// Builder: Serialization Target Object Abstraction
///
/// Monoidal (through `std::ops::Add`) string-builder
/// made up of raw bytes, that can be displayed as a hexstring
/// or a raw binary string
pub trait Builder
where
    Self: Add<Self, Output = Self> + AddAssign<Self> + Sized + From<Vec<u8>> + Target,
{
    type Segment;
    type Final: Into<Vec<u8>>;

    fn promote(seg: Self::Segment) -> Self;

    /// Constructor used for instantiating builders that consist of a single 8-bit word
    fn word(b: u8) -> Self;

    /// Constructor used for instantiating builders that consist of a fixed-size array of 8-bit words
    fn words<const N: usize>(b: [u8; N]) -> Self;

    fn finalize(self) -> Self::Final;

    /// Consume the Builder object and return a vector of its contents
    fn into_vec(self) -> Vec<u8> {
        self.finalize().into()
    }

    /// Return a string consisting of the raw hexadecimal sequence of words in the Builder
    fn into_hex(self) -> String {
        hex_of_bytes(self.into_vec().borrow())
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
}

pub mod memo;
pub mod strict;