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

use crate::parse::{ParseResult, Parser, ToParser};

use self::target::Target;

pub mod len;
pub mod target;

#[macro_export]
macro_rules! write_all_to {
    ( $($x:expr),* $(,)? => $tgt:expr ) => {
        { $( $x.write_to($tgt) + )* $crate::conv::target::resolve_zero($tgt) }
    };
}

/// Trait that marks a type as having a known binary encoding scheme in the `data-encoding` OCaml library,
/// and provides methods for serializing values of that type to various destination objects.
///
/// While only the [`write`] method is required, `to_bytes` and `encode` may be inefficient for certain
/// types, and their default implementation should be overwritten if appropriate.
pub trait Encode {
    /// Append the bytes of the serialized form of `self` to the end of the provided `Target` type.
    ///
    /// The natural definition of this method is structurally inductive on the physical or virtual fields
    /// of the type in question, in conformance with the serialization format defined by `data-encoding`.
    ///
    /// Sequential calls to this method are intended to operate on the same underlying Target, rather
    /// than separate Target objects that are later concatenated.
    ///
    fn write_to<U: Target>(&self, buf: &mut U) -> usize;

    /// Variant of [`write_to`] that is specialized to `Vec<u8>`.
    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        let _ = self.write_to(buf);
        return;
    }

    fn encode<U: Target>(&self) -> U {
        let mut tgt: U = U::create();
        write_all_to!(self => &mut tgt);
        tgt
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.encode::<Vec<u8>>()
    }
}

pub trait EncodeLength: Encode {
    fn enc_len(&self) -> usize {
        self.write_to(&mut std::io::sink())
    }

    fn to_bytes_full(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.enc_len());
        self.write_to(&mut buf);
        buf
    }
}

impl<T: Encode + len::Estimable + ?Sized> EncodeLength for T {
    fn enc_len(&self) -> usize {
        self.estimate()
    }
}

pub trait Decode {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized;

    fn try_decode<U, P>(inp: U) -> ParseResult<Self>
    where
        Self: Sized,
        P: Parser,
        U: ToParser<P>,
    {
        let mut p = inp.into_parser();
        Self::parse(&mut p)
    }

    fn decode_memo<U>(inp: U) -> Self
    where
        Self: Sized,
        U: ToParser<crate::parse::memoparser::MemoParser>,
    {
        Self::try_decode(inp).expect(&format!(
            "<{} as Decode>::decode_memo: unable to parse value (ParseError encountered)",
            std::any::type_name::<Self>()
        ))
    }

    fn decode<U>(inp: U) -> Self
    where
        Self: Sized,
        U: ToParser,
    {
        Self::try_decode(inp).expect(&format!(
            "<{} as Decode>::decode: unable to parse value (ParseError encountered)",
            std::any::type_name::<Self>()
        ))
    }
}

impl Encode for Vec<u8> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(&self) + crate::resolve_zero(buf)
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.get_dynamic(p.len() - p.offset())
    }
}

impl Encode for &str {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(self.as_bytes()) + crate::resolve_zero(buf)
    }
}

impl Encode for String {
    fn write_to<W: Target>(&self, buf: &mut W) -> usize {
        buf.push_all(self.as_bytes()) + crate::resolve_zero(buf)
    }
}

impl Decode for String {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buf: Vec<u8> = p.get_dynamic(p.len() - p.offset())?;

        Ok(String::from_utf8(buf)?)
    }
}

impl<T: Encode> Encode for Option<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        (match self {
            Some(val) => buf.push_one(0xff) + val.write_to(buf),
            None => buf.push_one(0x00),
        }) + crate::resolve_zero(buf)
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
    use crate::{Builder, Encode, StrictBuilder};

    #[test]
    fn check() {
        assert_eq!(
            "foo"
                .encode::<StrictBuilder>()
                .finalize()
                .into_bin()
                .unwrap(),
            "foo"
        );
    }
}
