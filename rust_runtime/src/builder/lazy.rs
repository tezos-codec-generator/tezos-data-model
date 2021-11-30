use std::ops::AddAssign;
use std::{borrow::Borrow, ops::Add};

use std::boxed::Box;
use std::collections::LinkedList;

type Thunk<'a> = Box<dyn FnMut(&mut Vec<u8>) + 'a>;

pub struct AtomicWrite<'a> {
    nbytes: usize,
    thunk: Thunk<'a>,
}

impl<'a> AtomicWrite<'a> {
    pub fn apply(mut self, buf: &mut Vec<u8>) {
        (self.thunk)(buf);
    }

    pub fn new(thunk: Thunk<'a>, nbytes: usize) -> Self {
        Self { nbytes, thunk }
    }

    #[allow(dead_code)]
    pub fn from_word(word: u8) -> Self {
        Self {
            nbytes: 1,
            thunk: Box::new(move |buf: &mut Vec<u8>| buf.push(word)),
        }
    }

    #[allow(dead_code)]
    pub fn from_words(words: &'a [u8]) -> Self {
        Self {
            nbytes: words.len(),
            thunk: Box::new(move |buf| buf.extend_from_slice(words)),
        }
    }
}

pub enum LazySegment<'a> {
    Opaque(AtomicWrite<'a>),
    Ephemeral(&'a [u8]),
    Allocated(Vec<u8>),
    Word(u8),
}

impl<'a> LazySegment<'a> {
    fn len(&self) -> usize {
        match self {
            &LazySegment::Opaque(AtomicWrite { nbytes, .. }) => nbytes,
            &LazySegment::Ephemeral(eph) => eph.len(),
            LazySegment::Allocated(buf) => buf.len(),
            &LazySegment::Word(_) => 1,
        }
    }

    fn manifest(self, buf: &mut Vec<u8>) {
        match self {
            LazySegment::Opaque(aw) => aw.apply(buf),
            LazySegment::Ephemeral(eph) => buf.extend_from_slice(eph),
            LazySegment::Allocated(mut extra) => buf.append(&mut extra),
            LazySegment::Word(word) => buf.push(word),
        }
    }

    fn promote(self) -> LazyBuilder<'a> {
        let len = self.len();
        LazyBuilder {
            len,
            segments: LinkedList::from([self]),
        }
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for LazySegment<'a> {
    fn from(words: &'a [u8; N]) -> Self {
        Self::Ephemeral(words as &'a [u8])
    }
}

impl<const N: usize> From<[u8; N]> for LazySegment<'_> {
    fn from(arr: [u8; N]) -> Self {
        Self::Allocated(arr.to_vec())
    }
}

impl<'a> From<&'a [u8]> for LazySegment<'a> {
    fn from(words: &'a [u8]) -> Self {
        Self::Ephemeral(words)
    }
}

impl From<Vec<u8>> for LazySegment<'_> {
    fn from(buf: Vec<u8>) -> Self {
        Self::Allocated(buf)
    }
}

impl From<u8> for LazySegment<'_> {
    fn from(word: u8) -> Self {
        Self::Word(word)
    }
}

pub struct LazyBuilder<'a> {
    len: usize,
    segments: LinkedList<LazySegment<'a>>,
}

impl<'a> LazyBuilder<'a> {
    fn from_segments(segments: LinkedList<LazySegment<'a>>) -> Self {
        let len = segments.iter().map(|x| x.len()).sum();
        Self { len, segments }
    }
}

impl<'a, T> From<T> for LazyBuilder<'a>
where
    LazySegment<'a>: From<T>,
{
    fn from(val: T) -> Self {
        LazySegment::from(val).promote()
    }
}

impl<'a> Into<Vec<u8>> for LazyBuilder<'a> {
    fn into(self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.len);
        for f in self.segments.into_iter() {
            f.manifest(&mut buf)
        }
        buf
    }
}

impl<'a> super::Builder for LazyBuilder<'a> {
    type Segment = LazySegment<'a>;
    type Final = super::strict::StrictBuilder;

    fn promote(seg: Self::Segment) -> Self {
        seg.promote()
    }

    fn empty() -> Self {
        Self::new()
    }

    fn word(b: u8) -> Self {
        b.into()
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.into()
    }

    fn finalize(self) -> Self::Final {
        <super::strict::StrictBuilder as From<Vec<u8>>>::from(self.into())
    }

    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> LazyBuilder<'a> {
    fn empty() -> Self {
        Self::from_segments(LinkedList::new())
    }

    pub fn new() -> Self {
        Self::empty()
    }

    pub fn push(&mut self, byte: u8) {
        self.len += 1;
        if let Some(last) = self.segments.pop_back() {
            match last {
                LazySegment::Opaque(_) | LazySegment::Ephemeral(_) => {
                    self.segments.push_back(last);
                    self.segments.push_back(LazySegment::from(byte));
                }
                LazySegment::Allocated(mut v) => {
                    v.push(byte);
                    self.segments.push_back(LazySegment::Allocated(v));
                }
                LazySegment::Word(b) => self.segments.push_back(LazySegment::from([b, byte])),
            }
        } else {
            self.segments.push_back(LazySegment::from(byte));
        }
    }
}

impl<'a> super::TransientBuilder<'a> for LazyBuilder<'a> {
    fn delayed(thunk: impl 'a + FnMut(&mut Vec<u8>), len: usize) -> Self {
        LazySegment::Opaque(AtomicWrite::new(Box::new(thunk), len)).promote()
    }
}

impl<'a> Add<LazyBuilder<'a>> for LazyBuilder<'a> {
    type Output = Self;

    fn add(mut self, mut rhs: LazyBuilder<'a>) -> Self::Output {
        self.len += rhs.len;
        self.segments.append(&mut rhs.segments);
        self
    }
}

impl<'a> AddAssign<LazyBuilder<'a>> for LazyBuilder<'a> {
    fn add_assign(&mut self, mut rhs: LazyBuilder<'a>) {
        self.len += rhs.len;
        self.segments.append(&mut rhs.segments);
    }
}

impl<'a, T: 'a + Borrow<[u8]>> Add<T> for LazyBuilder<'a> {
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        let nbytes = rhs.borrow().len();
        let thunk = Box::new(move |buf: &mut Vec<u8>| {
            buf.extend_from_slice(rhs.borrow());
        });
        let aw = AtomicWrite { nbytes, thunk, };

        <LazyBuilder as Add<LazyBuilder>>::add(
            self,
            LazySegment::Opaque(aw).promote(),
        )
    }
}

#[cfg(test)]
mod test {
    use crate::{builder::TransientBuilder, Builder};

    use super::*;

    #[test]
    fn check() {
        let mut accum = LazyBuilder::empty();
        accum += LazyBuilder::delayed(|v| v.extend(b"hello"), 5);
        accum += LazyBuilder::from(b" ");
        accum += LazyBuilder::from(b"world");
        accum += LazyBuilder::from(b"!");
        assert_eq!(
            accum.finalize().into_bin(),
            Ok(String::from("hello world!"))
        );
    }
}
