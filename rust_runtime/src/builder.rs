use std::{borrow::Borrow, string::FromUtf8Error};

use crate::util::hex_of_bytes;

/// Builder: Serialization Target Object Abstraction
/// 
/// Monoidal (through `std::ops::Add`) string-builder
/// made up of raw bytes, that can be displayed as a hexstring
/// or a raw minary string
pub trait Builder
where
    Self: Borrow<[u8]> + Clone + std::ops::Add<Self, Output = Self>,
{
    /// Constructor used for instantiating builders that consist of a single 8-bit word
    fn word(b: u8) -> Self;

    /// Constructor used for instantiating builders that consist of a fixed-size array of 8-bit words
    fn words<const N: usize>(b: [u8; N]) -> Self;

    /// Consume the Builder object and return a vector of its contents
    fn into_vec(self) -> Vec<u8>;

    // Return a string consisting of the raw hexadecimal sequence of words in the Builder
    fn show_hex(&self) -> String {
        hex_of_bytes(self.borrow())
    }

    // Attempt to convert the Builder object into a string in binary representation
    fn show(&self) -> Result<String, FromUtf8Error> {
        String::from_utf8(self.clone().into_vec())
    }
}

pub mod owned {
    use std::{borrow::Borrow, ops::Add};

    pub struct OwnedBuilder {
        buf: Vec<u8>,
    }

    impl From<u8> for OwnedBuilder {
        fn from(word: u8) -> Self {
            Self { buf: vec![word] }
        }
    }

    impl<const N: usize> From<[u8; N]> for OwnedBuilder {
        fn from(words: [u8; N]) -> Self {
            Self {
                buf: words.to_vec(),
            }
        }
    }

    impl<const N: usize> From<&[u8; N]> for OwnedBuilder {
        fn from(words: &[u8; N]) -> Self {
            Self {
                buf: words.to_vec(),
            }
        }
    }

    impl From<Vec<u8>> for OwnedBuilder {
        fn from(buf: Vec<u8>) -> Self {
            Self { buf }
        }
    }

    impl Into<Vec<u8>> for OwnedBuilder {
        fn into(self) -> Vec<u8> {
            self.buf
        }
    }

    impl Borrow<[u8]> for OwnedBuilder {
        fn borrow(&self) -> &[u8] {
            self.buf.borrow()
        }
    }

    impl Clone for OwnedBuilder {
        fn clone(&self) -> Self {
            Self {
                buf: self.buf.clone(),
            }
        }
    }

    impl super::Builder for OwnedBuilder {
        fn word(b: u8) -> Self {
            b.into()
        }

        fn words<const N: usize>(b: [u8; N]) -> Self {
            b.into()
        }

        fn into_vec(self) -> Vec<u8> {
            self.into()
        }
    }

    impl OwnedBuilder {
        pub fn empty() -> Self {
            Self { buf: Vec::new() }
        }

        pub fn new(cap: usize) -> Self {
            Self {
                buf: Vec::with_capacity(cap),
            }
        }

        pub fn push(&mut self, byte: u8) {
            self.buf.push(byte);
        }

        pub fn append<T: Borrow<[u8]>>(&mut self, extra: T) {
            self.buf.extend_from_slice(extra.borrow());
        }
    }

    impl Extend<u8> for OwnedBuilder {
        fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
            self.buf.extend(iter);
        }
    }

    impl<T: Borrow<[u8]>> Add<T> for OwnedBuilder {
        type Output = Self;

        fn add(self, rhs: T) -> Self::Output {
            let mut buf: Vec<u8> = self.buf;
            buf.extend_from_slice(rhs.borrow());
            Self { buf }
        }
    }
}