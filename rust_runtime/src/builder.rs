use std::{borrow::Borrow, string::FromUtf8Error};

use crate::util::hex_of_bytes;

/// Builder: Serialization Target Object Abstraction
///
/// Monoidal (through `std::ops::Add`) string-builder
/// made up of raw bytes, that can be displayed as a hexstring
/// or a raw minary string
pub trait Builder
where
    Self: std::ops::Add<Self, Output = Self> + Sized + From<Vec<u8>>,
{
    type Final: Builder;

    /// Constructor used for instantiating builders that consist of a single 8-bit word
    fn word(b: u8) -> Self;

    /// Constructor used for instantiating builders that consist of a fixed-size array of 8-bit words
    fn words<const N: usize>(b: [u8; N]) -> Self;

    /// Consume the Builder object and return a vector of its contents
    fn into_vec(self) -> Vec<u8>;

    /// Return a string consisting of the raw hexadecimal sequence of words in the Builder
    fn into_hex(self) -> String {
        hex_of_bytes(self.into_vec().borrow())
    }

    fn finalize(self) -> Self::Final;

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

pub trait TransientBuilder<'a>: Builder {
    /// Construct a Builder object from a closure that writes data to a vector
    fn delayed(mut f: impl 'a + FnMut(&mut Vec<u8>) -> (), len: usize) -> Self {
        let mut raw = Vec::new();
        f(&mut raw);
        assert_eq!(len, raw.len());
        raw.into()
    }
}

pub mod lazy;
pub mod owned;
