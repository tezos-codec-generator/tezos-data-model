use std::{
    borrow::Borrow,
    collections::LinkedList,
    iter::FromIterator,
    ops::{Add, AddAssign},
};

use super::TransientBuilder;

pub struct OwnedSegment(Vec<u8>);

impl OwnedSegment {
    fn new(cap: usize) -> Self {
        Self(Vec::with_capacity(cap))
    }

    fn promote(self) -> OwnedBuilder {
        OwnedBuilder {
            len: self.0.len(),
            chunks: LinkedList::from([self]),
        }
    }
}

pub struct OwnedBuilder {
    len: usize,
    chunks: LinkedList<OwnedSegment>,
}

impl From<u8> for OwnedSegment {
    fn from(word: u8) -> Self {
        Self(vec![word])
    }
}

impl<const N: usize> From<[u8; N]> for OwnedSegment {
    fn from(words: [u8; N]) -> Self {
        Self(words.to_vec())
    }
}

impl<const N: usize> From<&[u8; N]> for OwnedSegment {
    fn from(words: &[u8; N]) -> Self {
        Self(words.to_vec())
    }
}

impl From<&[u8]> for OwnedSegment {
    fn from(words: &[u8]) -> Self {
        Self(words.to_vec())
    }
}

impl From<Vec<u8>> for OwnedSegment {
    fn from(buf: Vec<u8>) -> Self {
        Self(buf)
    }
}

impl Into<Vec<u8>> for OwnedSegment {
    fn into(self) -> Vec<u8> {
        self.0
    }
}

impl FromIterator<u8> for OwnedSegment {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl Clone for OwnedSegment {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> From<T> for OwnedBuilder
where
    OwnedSegment: From<T>
{
    fn from(val: T) -> Self {
        OwnedSegment::from(val).promote()
    }
}

impl super::Builder for OwnedBuilder {
    type Segment = OwnedSegment;
    type Final = Vec<u8>;

    fn empty() -> Self {
        let buf : OwnedSegment = OwnedSegment::new(Self::BUFSIZE);
        let chunks = LinkedList::from([buf]);
        Self { len: 0, chunks }
    }

    fn promote(seg: OwnedSegment) -> OwnedBuilder {
        seg.promote()
    }

    fn word(b: u8) -> Self {
        let mut ret = Self::empty();
        ret.push(b);
        ret
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        let mut ret = Self::empty();
        ret.extend(b);
        ret
    }

    fn finalize(self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.len);
        for mut ele in self.chunks {
            buf.append(&mut ele.0);
        }
        buf
    }

    fn len(&self) -> usize {
        self.len
    }
}

impl TransientBuilder<'_> for OwnedBuilder {}

impl OwnedBuilder {
    const BUFSIZE : usize = 1024;

    pub fn push(&mut self, byte: u8) {
        self.len += 1;
        if let Some(last) = self.chunks.back_mut() {
            last.0.push(byte);
        } else {
            self.chunks.push_back(OwnedSegment::from(byte));
        }
    }

    pub fn append<T: Borrow<[u8]>>(&mut self, extra: T) {
        self.extend(extra.borrow())
    }
}

impl Extend<u8> for OwnedBuilder {
    fn extend<T: IntoIterator<Item = u8>>(&mut self, iter: T) {
        for i in iter {
            self.push(i)
        }
    }
}

impl<'a> Extend<&'a u8> for OwnedBuilder {
    fn extend<T: IntoIterator<Item = &'a u8>>(&mut self, iter: T) {
        for &i in iter {
            self.push(i)
        }
    }
}

impl<T: Borrow<[u8]>> Add<T> for OwnedBuilder {
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        let mut ret = self;
        ret += rhs;
        ret
    }
}

impl<T: Borrow<[u8]>> AddAssign<T> for OwnedBuilder {
    fn add_assign(&mut self, rhs: T) {
        self.extend(rhs.borrow())
    }
}

impl AddAssign<OwnedBuilder> for OwnedBuilder {
    fn add_assign(&mut self, mut rhs: Self) {
        self.chunks.append(&mut rhs.chunks);
    }
}

impl Add<OwnedBuilder> for OwnedBuilder {
    type Output = Self;

    fn add(self, mut rhs: Self) -> Self::Output {
        let len =  self.len + rhs.len;
        let mut chunks = self.chunks;
        chunks.append(&mut rhs.chunks);
        Self { len, chunks }
    }
}