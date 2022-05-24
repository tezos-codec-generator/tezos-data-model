use std::{borrow::Borrow, ops::{Add, AddAssign}};

use crate::conv::target::Target;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StrictBuilder(Vec<u8>);

impl Borrow<[u8]> for StrictBuilder {
    fn borrow(&self) -> &[u8] {
        self.0.borrow()
    }
}

impl From<StrictBuilder> for Vec<u8> {
    fn from(val: StrictBuilder) -> Self {
        val.0
    }
}

impl From<Vec<u8>> for StrictBuilder {
    fn from(buf: Vec<u8>) -> StrictBuilder {
        StrictBuilder(buf)
    }
}

impl From<&[u8]> for StrictBuilder {
    fn from(buf: &[u8]) -> StrictBuilder {
        StrictBuilder(buf.into())
    }
}

impl Add<Self> for StrictBuilder {
    type Output = Self;

    fn add(self, mut rhs: Self) -> Self::Output {
        let mut buf = self.0;
        buf.append(&mut rhs.0);
        Self(buf)
    }
}

impl AddAssign<Self> for StrictBuilder {
    fn add_assign(&mut self, mut rhs: Self)  {
        self.0.append(&mut rhs.0);
    }
}

impl std::io::Write for StrictBuilder {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

impl Target for StrictBuilder {
    fn anticipate(&mut self, extra: usize) {
        self.0.anticipate(extra)
    }

    fn push_one(&mut self, b: u8) -> usize {
        self.0.push_one(b)
    }

    fn push_all(&mut self, buf: &[u8]) -> usize {
        self.0.push_all(buf)
    }

    fn resolve(&mut self) {
        self.0.resolve()
    }

    fn push_many<const N: usize>(&mut self, arr: [u8; N]) -> usize {
        self.0.push_many(arr)
    }

    fn create() -> Self {
        Self(Vec::create())
    }
}


impl crate::Builder for StrictBuilder {
    type Segment = Self;

    type Final = Self;

    fn promote(seg: Self::Segment) -> Self {
        seg
    }

    fn word(b: u8) -> Self {
        vec![b].into()
    }

    fn words<const N: usize>(b: [u8; N]) -> Self {
        b.to_vec().into()
    }

    fn finalize(self) -> Self::Final {
        self
    }

    fn len(&self) -> usize {
        Vec::len(&self.0)
    }
}