use std::{
    borrow::Borrow,
    collections::LinkedList,
    ops::{Add, AddAssign},
};

use super::{Builder, TransientBuilder};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoSegment(Vec<u8>);

impl IntoIterator for MemoSegment {
    type Item = u8;

    type IntoIter = std::vec::IntoIter<u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Borrow<[u8]> for MemoSegment {
    fn borrow(&self) -> &[u8] {
        self.0.borrow()
    }
}

impl Into<Vec<u8>> for MemoSegment {
    fn into(self) -> Vec<u8> {
        self.0
    }
}

impl From<Vec<u8>> for MemoSegment {
    fn from(buf: Vec<u8>) -> Self {
        Self(buf)
    }
}

impl From<&[u8]> for MemoSegment {
    fn from(buf: &[u8]) -> Self {
        Self(buf.into())
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct MemoBuilder {
    totlen: usize,
    segs: LinkedList<MemoSegment>,
}

impl std::fmt::Debug for MemoBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoBuilder")
            .field("segs", &self.segs)
            .finish()
    }
}

impl Into<Vec<u8>> for MemoBuilder {
    fn into(self) -> Vec<u8> {
        self.segs.into_iter().flatten().collect()
    }
}

impl From<Vec<u8>> for MemoBuilder {
    fn from(buf: Vec<u8>) -> Self {
        Self {
            totlen: buf.len(),
            segs: LinkedList::from([buf.into()]),
        }
    }
}

impl From<&[u8]> for MemoBuilder {
    fn from(buf: &[u8]) -> MemoBuilder {
        Self::from(<&[u8] as Into<Vec<u8>>>::into(buf))
    }
}

impl Add<Self> for MemoBuilder {
    type Output = Self;

    fn add(self, mut rhs: Self) -> Self::Output {
        let mut buf = self.segs;
        buf.append(&mut rhs.segs);
        Self {
            totlen: self.totlen + rhs.totlen,
            segs: buf,
        }
    }
}

impl AddAssign<Self> for MemoBuilder {
    fn add_assign(&mut self, mut rhs: Self) {
        self.totlen += rhs.totlen;
        self.segs.append(&mut rhs.segs);
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoBuffer {
    lens: Vec<usize>,
    buf: Vec<u8>,
}

impl Into<Vec<u8>> for MemoBuffer {
    fn into(self) -> Vec<u8> {
        self.buf
    }
}

impl std::fmt::Debug for MemoBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoBuffer")
            .field("lens", &self.lens)
            .field("buf", &self.buf)
            .finish()
    }
}

impl std::fmt::Display for MemoBuffer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buf: &[u8] = &self.buf[..];
        write!(f, "[|")?;
        let mut ls = self.lens.iter();
        while let Some(&l) = ls.next() {
            write!(f, "{:#?}|", &buf[..l])?;
            buf = &buf[l..];
        }
        write!(f, "]")
    }
}

impl Builder for MemoBuilder {
    type Segment = MemoSegment;

    type Final = MemoBuffer;

    fn promote(seg: Self::Segment) -> Self {
        Self {
            totlen: seg.0.len(),
            segs: LinkedList::from([seg]),
        }
    }

    fn word(b: u8) -> Self {
        vec![b].into()
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.to_vec().into()
    }

    fn finalize(self) -> Self::Final {
        let mut lens: Vec<usize> = Vec::with_capacity(self.segs.len());
        let mut buf: Vec<u8> = Vec::with_capacity(self.totlen);
        for seg in self.segs {
            lens.push(seg.0.len());
            buf.extend(seg.0.iter());
        }
        MemoBuffer { lens, buf }
    }

    fn len(&self) -> usize {
        self.totlen
    }
}

impl TransientBuilder<'_> for MemoBuilder {}
