use std::ops::AddAssign;
use std::{borrow::Borrow, ops::Add};

use std::boxed::Box;
use std::collections::LinkedList;

pub struct LazySegment<'a> {
    len: usize,
    manifest: Box<dyn FnMut(&mut Vec<u8>) -> () + 'a>,
}

impl<'a> LazySegment<'a> {
    pub fn new(f: impl FnMut(&mut Vec<u8>) -> () + 'a, len: usize) -> Self {
        Self {
            len,
            manifest: Box::new(f),
        }
    }

    fn promote(self) -> LazyBuilder<'a> {
        let mut segments = LinkedList::new();
        segments.push_front(self);
        LazyBuilder::from_segments(segments)
    }
}

pub struct LazyBuilder<'a> {
    len: usize,
    segments: LinkedList<LazySegment<'a>>,
}

impl<'a> LazyBuilder<'a> {
    fn from_segments(segments: LinkedList<LazySegment<'a>>) -> Self {
        let len = segments.iter().map(|x| x.len).sum();
        Self { len, segments }
    }
}

impl<'a> From<u8> for LazySegment<'a> {
    fn from(word: u8) -> Self {
        Self::new(move |v: &mut Vec<u8>| v.push(word), 1)
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for LazySegment<'a> {
    fn from(words: &'a [u8; N]) -> Self {
        Self::new(move |v: &mut Vec<u8>| v.extend(words), N)
    }
}
impl<'a, const N: usize> From<[u8; N]> for LazySegment<'a> {
    fn from(words: [u8; N]) -> Self {
        Self::new(move |v: &mut Vec<u8>| v.extend(words), N)
    }
}

impl<'a> From<Vec<u8>> for LazySegment<'a> {
    fn from(mut buf: Vec<u8>) -> Self {
        let len = buf.len();
        Self::new(move |v: &mut Vec<u8>| v.append(&mut buf), len)
    }
}

impl<'a> From<&'a [u8]> for LazySegment<'a> {
    fn from(words: &'a [u8]) -> Self {
        let len = words.len();
        Self::new(move |v: &mut Vec<u8>| v.extend(words), len)
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
        for mut f in self.segments {
            (*f.manifest)(&mut buf);
        }
        buf
    }
}

impl<'a> super::Builder for LazyBuilder<'a> {
    type Final = super::owned::OwnedBuilder;

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
        super::owned::OwnedBuilder::from(self.into_vec())
    }


    fn into_vec(self) -> Vec<u8> {
        self.into()
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
        self.segments.push_back(LazySegment::from(byte));
    }
}

impl<'a> super::TransientBuilder<'a> for LazyBuilder<'a> {
    fn delayed(f: impl 'a + FnMut(&mut Vec<u8>) -> (), len: usize) -> Self {
        LazySegment::new(f, len).promote()
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
    fn add_assign(&mut self, mut rhs: LazyBuilder<'a>)  {
        self.len += rhs.len;
        self.segments.append(&mut rhs.segments);
    }
}

impl<'a, T: 'a + Borrow<[u8]>> Add<T> for LazyBuilder<'a> {
    type Output = Self;

    fn add(self, rhs: T) -> Self::Output {
        let len = rhs.borrow().len();
        let f = move |buf: &mut Vec<u8>| {
            buf.extend_from_slice(rhs.borrow());
        };

        <LazyBuilder as Add<LazyBuilder>>::add(self, LazySegment::new(f, len).promote())
    }
}

#[cfg(test)]
mod test {
    use crate::{Builder, builder::TransientBuilder};

    use super::*;

    #[test]
    fn check() {
        let mut accum = LazyBuilder::empty();
        accum += LazyBuilder::delayed(|v| v.extend(b"hello"), 5);
        accum += LazyBuilder::from(b" ");
        accum += LazyBuilder::from(b"world");
        accum += LazyBuilder::from(b"!");
        assert_eq!(accum.finalize().into_bin(), Ok(String::from("hello world!")));
    }

}