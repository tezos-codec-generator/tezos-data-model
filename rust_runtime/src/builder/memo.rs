use std::{
    ops::{Add, AddAssign},
};

use crate::{conv::target::Target, internal::SplitVec, util::hex_of_bytes};

use super::Builder;
#[derive(Clone)]
pub struct MemoBuilder {
    segs: SplitVec<u8>,
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
        self.segs.forget()
    }
}

impl From<Vec<u8>> for MemoBuilder {
    fn from(buf: Vec<u8>) -> Self {
        Self {
            segs: SplitVec::promote_vec(buf),
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

    fn add(self, rhs: Self) -> Self::Output {
        let mut buf = self.segs;
        buf.concat(rhs.segs);
        Self { segs: buf }
    }
}

impl AddAssign<Self> for MemoBuilder {
    fn add_assign(&mut self, rhs: Self) {
        self.segs.concat(rhs.segs);
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoBuffer {
    lens: Vec<usize>,
    buf: Vec<u8>,
}

impl From<SplitVec<u8>> for MemoBuffer {
    fn from(val: SplitVec<u8>) -> Self {
        Self {
            lens: val.spans.into_iter().collect(),
            buf: val.buffer,
        }
    }
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
            write!(f, "{}|", hex_of_bytes(&buf[..l]))?;
            buf = &buf[l..];
        }
        write!(f, "]")
    }
}

impl std::io::Write for MemoBuilder {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let ret = buf.len();

        self.segs.extend_current(buf.iter().copied());

        Ok(ret)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }

    fn write_all(&mut self, mut buf: &[u8]) -> std::io::Result<()> {
        if !buf.is_empty() {
            self.segs.split()
        };
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => {
                    panic!("failed to write whole buffer");
                }
                Ok(n) => buf = &buf[n..],
                Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

impl Target for MemoBuilder {
    #[inline]
    fn anticipate(&mut self, n: usize) {
        self.segs.buffer.reserve_exact(n)
    }

    #[inline]
    fn push_one(&mut self, b: u8) -> usize {
        self.segs.push_current(b);
        1
    }

    #[inline]
    fn push_all(&mut self, buf: &[u8]) -> usize {
        let l = buf.len();
        self.segs.extend_current(buf.iter().copied());
        l
    }

    fn resolve(&mut self) {
        self.segs.split();
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.segs.extend_current(arr.iter().copied());
        N
    }

    #[inline]
    fn create() -> Self {
        Self {
            segs: SplitVec::new(),
        }
    }
}

impl Builder for MemoBuilder {
    type Segment = Vec<u8>;

    type Final = MemoBuffer;

    fn promote(seg: Self::Segment) -> Self {
        Self {
            segs: SplitVec::promote_vec(seg),
        }
    }

    fn word(b: u8) -> Self {
        vec![b].into()
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.to_vec().into()
    }

    fn finalize(self) -> Self::Final {
        self.segs.into()
    }

    fn len(&self) -> usize {
        self.segs.buffer.len()
    }
}
