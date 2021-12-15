use crate::conv::{len, Decode, Encode};
use crate::parse::byteparser::{Parser, ParseResult};
use std::ops::DerefMut;
use std::{self, ops::Deref};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bytes(Vec<u8>);

impl len::ScalarLength for Bytes {
    type Elem = u8;

    const PER_ELEM: usize = 1;

    fn n_elems(&self) -> usize {
        self.0.len()
    }
}

impl Deref for Bytes {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Into<Vec<u8>> for Bytes {
    fn into(self) -> Vec<u8> {
        self.0
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }
}

impl Encode for Bytes {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self.0.iter())
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.0.clone()
    }
}

impl Decode for Bytes {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        Ok(Self(Vec::<u8>::parse(p)?))
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sequence<T>(Vec<T>);

impl<T> Into<Vec<T>> for Sequence<T> {
    fn into(self) -> Vec<T> {
        self.0
    }
}

impl<T> From<Vec<T>> for Sequence<T> {
    fn from(seq: Vec<T>) -> Self {
        Self(seq)
    }
}

impl<T> Deref for Sequence<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Sequence<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: len::Estimable> len::Estimable for Sequence<T> {
    const KNOWN: Option<usize> = None;

    fn unknown(&self) -> usize {
        self.0.iter().map(len::Estimable::len).sum()
    }
}

impl<T: Encode> Encode for Sequence<T> {
    fn write(&self, buf: &mut Vec<u8>) {
        for item in &self.0 {
            item.write(buf);
        }
    }
}

impl<T: Decode> Decode for Sequence<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let mut seq: Vec<T> = Vec::new();

        while p.remainder() != 0 {
            seq.push(T::parse(p)?);
        }

        Ok(Self(seq))
    }
}
