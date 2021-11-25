use std::{
    borrow::Borrow,
    iter::FromIterator,
    ops::{Add, AddAssign},
};

use super::TransientBuilder;

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

impl FromIterator<u8> for OwnedBuilder {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self {
            buf: Vec::from_iter(iter),
        }
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
    type Final = Self;

    fn empty() -> Self {
        Self { buf: Vec::new() }
    }

    fn word(b: u8) -> Self {
        b.into()
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.into()
    }

    fn finalize(self) -> Self {
        self
    }

    fn into_vec(self) -> Vec<u8> {
        self.buf
    }

    fn len(&self) -> usize {
        self.buf.len()
    }
}

impl TransientBuilder<'_> for OwnedBuilder {}

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

impl<T: Borrow<[u8]>> AddAssign<T> for OwnedBuilder {
    fn add_assign(&mut self, rhs: T) {
        self.buf.extend_from_slice(rhs.borrow())
    }
}
