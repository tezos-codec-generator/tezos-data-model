use std::ops::DerefMut;
use std::{self, ops::Deref};
use crate::parse::byteparser::Parser;
use crate::conv::{Encode,Decode};
use crate::builder::Builder;

pub struct Bytes(Vec<u8>);

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
    fn encode<U: Builder>(&self) -> U {
        self.0.encode::<U>()
    }
}

impl Decode for Bytes {
    fn parse<P: Parser>(p: &mut P) -> Self {
        Self(Vec::<u8>::parse(p))
    }
}

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

impl<T: Encode> Encode for Sequence<T> {
    fn encode<U: Builder>(&self) -> U {
        let mut ret : U = U::words([]);
        for item in &self.0 {
            ret = ret + item.encode()
        }
        ret
    }
}

impl<T: Decode> Decode for Sequence<T> {
    fn parse<P: Parser>(p: &mut P) -> Self {
        let mut seq : Vec<T> = Vec::new();
        let l = p.len();

        while p.offset() != l {
            seq.push(T::parse(p));
        }

        Self(seq)
    }
}