use std::{borrow::Borrow, ops::{Add, AddAssign}};

use super::TransientBuilder;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct StrictBuilder(Vec<u8>);

impl Borrow<[u8]> for StrictBuilder {
    fn borrow(&self) -> &[u8] {
        self.0.borrow()
    }
}

impl Into<Vec<u8>> for StrictBuilder {
    fn into(self) -> Vec<u8> {
        self.0
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

impl TransientBuilder<'_> for StrictBuilder {}