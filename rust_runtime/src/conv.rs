//! `conv`: core functionality of the binary-conversion API
//!
//! This module provides the primary functionality of the runtime, the trait definitions
//! for `Encode` and `Decode`. These traits are the principal motivation for the existence
//! of a standalone runtime to begin with, and their API is by far the most important to respect
//! when substituting a variant runtime in the place of the implementations provided in this crate.
//!
//! While the internal implementations may change, this module exposes a comparatively stable API,
//! as the structures of Encode and Decode cannot be altered without drastic changes not only to the
//! remainder of the `runtime` crate itself, but also to the generator logic and even the domain-specific
//! AST in the `codec_generator` OCaml project code.
//!
//! The sub-module [`len`](./conv.len.html), which defines `Estimable` and its refinements, is also
//! a major feature of the runtime, but to a far lesser extent; it is possible to eliminate Estimable
//! entirely and code around it in certain places without much side-effect, while Encode and Decode
//! cannot be easily deprecated or phased out.
//!
//! Derive macros for Encode, Decode, and even Estimable are provided in the sub-crates `encode_derive`,
//! `decode_derive`, and `estimable_derive`, which are only relevant within the context of this runtime.

use crate::builder::{Builder, TransientBuilder};
use crate::parse::byteparser::{Parser, ToParser, ParseResult};

pub mod len;
/// Trait that marks a type as having a known binary encoding scheme in the `data-encoding` OCaml library,
/// and provides methods for serializing values of that type to various destination objects.
///
/// While only the [`write`] method is required, `to_bytes` and `encode` may be inefficient for certain
/// types, and their default implementation should be overwritten if appropriate.
pub trait Encode {
    /// Append the bytes of the serialized form of `self` to the end of the provided `Vec<u8>` buffer.
    ///
    /// This method allows for sequential or nested components of a complex type to be written directly
    /// into the existing buffer containing the serialized bytes of all preceding fragments, without
    /// having to allocate new heap memory (except if the vector cannot be extended in-place upon reaching
    /// its capacity)
    ///
    /// The natural definition of this method is structurally inductive on the physical or virtual fields
    /// of the type in question, in conformance with the serialization format defined by `data-encoding`.
    ///
    /// In principle, it is possible to redefine this method so that it operates on any `Writer` object rather
    /// than merely on `Vec<u8>`. The merits of this strategy will be evaluated and a decision on the correct
    /// approach will be rendered in due course.
    fn write(&self, buf: &mut Vec<u8>);

    /// Variant of [`write`] that can accept non-vector targets.
    ///
    /// The default implementation is somewhat inefficient, as it
    /// requires a two-pass approach of calling [`write`] on an
    /// empty vector and using [`std::io::Write::write_all`] to copy
    /// the serialized bytes from the vector using `std::io::copy`.
    fn write_any<W: std::io::Write>(&self, buf: &mut W) -> std::io::Result<u64> {
        let mut temp = Vec::new();
        self.write(&mut temp);
        std::io::copy(&mut &*temp as &mut &[u8], buf)
    }

    /// Create a new buffer and call `self.write` on it
    fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write(&mut buf);
        buf
    }

    fn encode<U: Builder>(&self) -> U {
        self.to_bytes().into()
    }
}

pub trait EncodeLength: Encode {
    fn enc_len(&self) -> usize {
        eprintln!("Warning: inefficient EncodeLength::enc_len() call on type {}!", std::any::type_name::<Self>());
        self.to_bytes().len()
    }

    fn to_bytes_full(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.enc_len());
        self.write(&mut buf);
        buf
    }

    fn lazy_encode<'a, U>(&'a self) -> U where U: TransientBuilder<'a> + 'a {
        U::delayed(move |buf| Encode::write(self, buf), self.enc_len())
    }
}

impl<T: Encode + len::Estimable + ?Sized> EncodeLength for T {
    fn enc_len(&self) -> usize {
        self.len()
    }
}

pub trait Decode {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where Self: Sized;

    fn decode<U: ToParser>(inp: U) -> Self
    where
        Self: Sized,
    {
        let mut p = inp.to_parser();
        Self::parse(&mut p).expect(&format!("<{} as Decode>::decode: unable to parse value (ParseError encountered): ", std::any::type_name::<Self>()))
    }
}

impl Encode for Vec<u8> {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self)
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.get_dynamic(p.len() - p.offset())
    }
}

impl Encode for &str {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self.bytes())
    }
}

impl Encode for String {
    fn write(&self, buf: &mut Vec<u8>) {
        buf.extend(self.bytes())
    }
}

impl Decode for String {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buf: Vec<u8> = p.get_dynamic(p.len() - p.offset())?;

        Ok(String::from_utf8(buf)?)
    }
}

impl<T: Encode> Encode for Option<T> {
    fn write(&self, buf: &mut Vec<u8>) {
        match self {
            Some(val) => {
                buf.push(0xff);
                val.write(buf);
            }
            None => {
                buf.push(0x00);
            }
        }
    }
}

impl<T: Decode> Decode for Option<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        match p.get_tagword::<Option<T>, u8>(&[0x00, 0xff])? {
            0xff => Ok(Some(T::parse(p)?)),
            0x00 => Ok(None),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Builder, LazyBuilder};

    use super::EncodeLength;

    #[test]
    fn check() {
        assert_eq!(
            "foo"
                .lazy_encode::<LazyBuilder>()
                .finalize()
                .into_bin()
                .unwrap(),
            "foo"
        );
    }
}
