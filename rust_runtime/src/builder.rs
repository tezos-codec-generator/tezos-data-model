use std::{borrow::Borrow, string::FromUtf8Error};

use crate::util::hex_of_bytes;

pub trait Builder
where
    Self: Borrow<[u8]> + Clone + std::ops::Add<Self, Output = Self>,
{
    fn word(b: u8) -> Self;

    fn words<const N: usize>(b: [u8; N]) -> Self;

    fn into_vec(self) -> Vec<u8>;

    fn show_hex(&self) -> String {
        hex_of_bytes(self.borrow())
    }

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
