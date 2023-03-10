//! Core of the binary-conversion API
//!
//! This module contains definitions for the high-level transcoding traits
//! `Encode` and `Decode`, which are motivationally equivalent to the
//! `Serialize` and `Deserialize` traits defined in `serde`.
//!
//! While a great deal of the underlying machinery of this crate is subject to customization
//! by end-users, such as the selection or novel definitions of `Parser` and `Target` implementations,
//! `Encode` and `Decode` serve as the core of this library. Any upstream library that does not use
//! `Encode` or `Decode` even indirectly, will ultimately derive little to no benefit from this library.
//!
//! While the internal implementations may change, this module exposes a comparatively stable API,
//! as the structures of `Encode` and `Decode` cannot be altered without drastic changes not only to the
//! remainder of the library itself, but also the abstract model, and generative logic used in the
//! `codec_generator` that this library is designed in tandem with.
//!
//! The sub-module [`len`], which defines `Estimable` and its refinements, is also
//! a major feature of the runtime, but to a far lesser extent; it is possible to eliminate Estimable
//! entirely and code around it in certain places without much side-effect, while Encode and Decode
//! are fundamental enough that they would be nearly impossible to deprecate without significantly
//! reducing the usefulness of this library.
//!
//! An additional submodule, [`target`], offers an abstraction along the lines of [`std::io::Write`], namely the
//! [`target::Target`] trait. This is the dual to [`crate::parse::Parser`], acting as the generic
//! bound for serialization in the [`Decode::write_to`] method, among others.
//!
//! Derive macros for Encode, Decode, and even Estimable are provided in the sub-crates `encode_derive`,
//! `decode_derive`, and `estimable_derive`, which are only relevant within the context of this library,
//! and otherwise offer no standalone functionality.

use crate::parse::{ ParseResult, Parser, TryIntoParser };

use self::target::Target;

pub mod error;
pub mod len;
pub mod target;

pub use error::DecodeResult;

#[macro_export]
macro_rules! write_all_to {
    ($($x:expr),* $(,)? => $tgt:expr) => {
        { $( $x.write_to($tgt) + )* $crate::conv::target::Target::resolve_zero($tgt) }
    };
}

/// Trait for types that support serialization into an Octez-interoperable binary form
///
/// The `Encode` trait is used for types that act as Rust-local analogues of Tezos protocol
/// types as defined in Octez, and for which there is a corresponding conversion process from
/// the language-bound value to a cross-language interoperable binary format, based on the
/// appropriate encoding scheme based in the `data-encoding` (OCaml) library.
///
/// Implementing [`Encode`] can be as simple as providing a definition of the required method
/// [`write_to`], but for types that have efficient overrides for the other default-implemented
/// methods, such optimizations are recommended as long as the implementations conform to the
/// specified invariants of each method.
///
/// If the implementing type can implement the remaining methods more efficiently than
/// the default implementations allow for, it is recommended to override them, provided
/// the operational semantics are left unchanged.
///
/// [`Target`]: crate::conv::target::Target
pub trait Encode {
    /// Appends the serialized bytes of this value to a generic buffer,
    /// returning the exact number of bytes written
    ///
    /// Morally related to the trait method [`std::io:Write::write`], with the caveat
    /// that `write_to` should be infallible under almost all operating conditions,
    /// as well as being generic over any buffer that satisfies the trait-bound of
    /// [`Target`][crate::conv::target::Target].
    ///
    /// The natural definition of this method is structurally inductive on the
    /// physical or virtual fields of the type in question, in conformance with
    /// the serialization format defined by `data-encoding`.
    fn write_to<U: Target>(&self, buf: &mut U) -> usize;

    /// Appends the serialized bytes of this value to a monomorphized [`Vec<u8>`] buffer.
    ///
    /// This method is a specialized variant of [`write_to`] for `Vec<u8>` targets, that
    /// may be overridden if there is an efficient implementation for that specific case.
    ///
    /// As a partial specialization, this method also does not return the number of bytes
    /// written to the vector, as such book-keeping may impose unnecessary overhead on
    /// overridden implementations that would normally be more efficient than [`write_to`].
    #[inline]
    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        let _ = self.write_to(buf);
    }

    /// Creates a new buffer and fills it with the serialized bytes of this value.
    ///
    /// If Rust ever supports specialization, this method may be overridden to provide
    /// more efficient implementations than the default. As it is, however, the default
    /// implementation is not expected to be less efficient than any potential override,
    /// due to the generic nature of the return type.
    #[must_use]
    #[inline]
    fn encode<U: Target>(&self) -> U {
        let mut buf: U = U::create();
        let _ = self.write_to::<U>(&mut buf);
        buf
    }

    /// Creates a [`Vec<u8>`] and fills it with the serialized bytes of this value.
    ///
    /// If the number of bytes required for the serialization of a given value can
    /// be determined in advance (e.g. through the [`Estimable`][crate::conv::len::Estimable] trait family),
    /// then the initial allocation can be optimized for that size to avoid amortized reallocation costs.
    ///
    /// # Note
    ///
    /// A related method on an extension trait, specifically [`EncodeLength::to_bytes_full`],
    /// will typically outperform this method even in its default implementation. However, both
    /// methods may benefit from implementation-specific overrides if the size of the serialized buffer
    /// can be precomputed cheaply. In that case, the initial allocation can be tailored to the ultimate
    /// maximum capacity required for the buffer, so that reallocation costs are avoided.
    #[must_use]
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write_to_vec(&mut buf);
        buf
    }
}

/// Extension trait for `Encode` that makes use of serialization-length oracles
///
/// This trait defines additional methods on an `Encode` type, which can determine
/// the exact number of bytes in the serialized version of a value without requiring
/// allocations, as well as an optimization of [`Encode::to_bytes`] that
/// makes use of this prediction to avoid reallocation costs.
pub trait EncodeLength: Encode {
    /// Computes, without allocation, the number of bytes in the serialized
    /// form of `self`, based on the implementation of [`Encode::write_to`].
    ///
    /// The default implementation of this method invokes [`write_to`] over the
    /// zero-allocation target [`ByteCounter`], whose return value is the number
    /// of bytes that were 'written'.
    ///
    /// # Optimization
    ///
    /// If the feature flag `enc_len_estimable_override` is enabled, the default
    /// implementation is automatically overridden in the blanket implemenation
    /// of `EncodeLength` over `Encode`-types that implement [`Estimable`] as well,
    /// using the [`estimate`] method of that trait.
    ///
    /// ## Relative Performance
    ///
    /// It is not known at this time under what circumstances either the default
    /// implementation, or that override, is more efficent than the other, or by
    /// what factor.
    ///
    /// [`Estimable`]: len::Estimable
    /// [`estimate`]: len::Estimable::estimate
    #[must_use]
    #[inline]
    fn enc_len(&self) -> usize {
        self.write_to(&mut std::io::sink())
    }

    /// Pre-determines the exact number of bytes required to serialize `self`,
    /// and returns a `Vec<u8>` initialized to that capacity, which contains
    /// the serialized bytes of `self`
    ///
    /// Assuming that there is no inconsistency or error in the implementation
    /// of [`enc_len`], the default implementation of this method should perform
    /// zero reallocations while populating the novel vector.
    #[must_use]
    fn to_bytes_full(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.enc_len());
        self.write_to_vec(&mut buf);
        buf
    }
}

impl<T: Encode + len::Estimable + ?Sized> EncodeLength for T {
    #[cfg(feature = "enc_len_estimable_override")]
    /// Computes, without allocation, the number of bytes in the serialized
    /// form of `self`, based on the implementation of [`Encode::write_to`].
    ///
    /// # Implementation
    ///
    /// This method's default implementation has been overridden
    /// using the method [`Estimable::estimate`]
    ///
    /// [`Estimable::estimate`]: len::Estimable::estimate
    fn enc_len(&self) -> usize {
        self.estimate()
    }
}

/// Trait providing methods for deserializing binary data into values of a certain type
///
/// This trait should only be implemented on types for which there is
/// a standard binary encoding scheme within the `data-encoding` OCaml library.
///
/// It is almost always expected that a type implementing `Decode` will also
/// implement [`Encode`], although this is not enforced at any level except
/// in certain contexts, where both traits may appear as simulataneous bounds
/// on generic types.
///
/// Implementations are defined by one required method, [`parse`]:
///     * The `parse` method attempts to consume the contextually
///     appropriate number of bytes from a [`Parser`] type, either
///     returning a valid value of the implementing type that was
///     interpreted from the consumed sequence, or an error if
///     parsing either failed, or yielded a value that was determined to
///     be invalid.
///
/// # Derive Macro
///
/// This crate provides a derive-macro `Decode` that is suitable for
/// implementing `Decode` on user-defined types, with the exception of
/// `enum` and `union` types.
///
/// No strategy has yet been devised for handling `Decode` on undiscriminated
/// unions.
///
/// In order to implement `Derive` automatically on user-generated enum-types,
/// see the [`adt`](crate::adt) module for an alternate strategy.
///
/// # Example
///
/// A typical hand-written implementation of `Decode` is provided below:
///
/// ```
/// # use ::tedium::parse::{Parser, ParseResult, byteparser::ByteParser};
/// use tedium::Decode;
/// use tedium::{VPadded, Bytes, Sequence, seq};
///
/// #[derive(Debug, PartialEq)]
/// pub struct MyTypeElem {
///     is_valid: bool,
///     id: u8,
/// }
///
/// #[derive(Debug, PartialEq)]
/// pub struct MyType(Sequence<MyTypeElem>);
///
/// impl Decode for MyTypeElem {
///     fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
///         Ok(Self { is_valid: bool::parse(p)?,
///                   id: u8::parse(p)?,
///                 }
///         )
///     }
/// }
///
/// impl Decode for MyType {
///     fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
///         Ok(Self(Sequence::<MyTypeElem>::parse(p)?))
///     }
/// }
///
/// fn main() {
///     assert_eq!(MyType(seq![MyTypeElem { is_valid: true, id: 42 }]), <MyType as Decode>::decode(vec![0xff, 0x2a]));
/// }
/// ```
pub trait Decode {
    /// Attempt to consume and interpret a value of type `Self` from an existing
    /// `Parser` object over a binary buffer.
    ///
    /// # Errors
    ///
    /// In most cases, the errors returned by this method will be propogated from
    /// calls made to [`Parser`] methods in the implementation logic.
    ///
    /// In rare cases, it may be necessary to return newly minted `ParseError`
    /// values based on certain invariants of the type being parsed.
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> where Self: Sized;

    /// Attempt to decode a value of the `Self` type from a value `input` of the
    /// generic type `U: TryIntoParser<P>`.
    ///
    /// The default implementation of this method produces a novel `P: Parser` object
    /// from `input` and calls [`parse`] on it.
    ///
    /// # Errors
    ///
    /// As [`TryIntoParser::try_into_parser`] and [`parse`] are both fallible methods,
    /// this method will, by default, propogate any error returned by either.
    ///
    /// In addition, if the feature-flag `check_complete_parse` is enabled,
    /// the [`cleanup`](crate::parse::Parser::cleanup) method is called on
    /// the leftover `P`-value that would otherwise be dropped when this
    /// method returns, to ensure that it is in a coherent state with no leftover bytes.
    /// If this method call returns an error, or returns successfully but indicates
    /// an incomplete parse, an appropriate [`DecodeError`] will be returned.
    fn try_decode<U, P>(input: U) -> DecodeResult<Self>
        where Self: Sized, P: Parser, U: TryIntoParser<P>, error::DecodeError: From<U::Error>
    {
        let mut p: P = input.try_into_parser()?;
        let ret = Self::parse(&mut p)?;
        #[cfg(feature = "check_complete_parse")]
        {
            let res: crate::parse::cleanup::LeftoverState = p.cleanup()?;
            if !res.is_empty() {
                return Err(error::DecodeError::NonEmpty(res));
            }
        }
        Ok(ret)
    }

    /// Decodes a value of type `Self` from a value `input` of the generic
    /// type `U: TryIntoParser<MemoParser>`, using [`MemoParser`] as the
    /// `Parser` type internally.
    ///
    /// This is intended primarily for debugging purposes, as `MemoParser`
    /// includes debugging information on failure at the cost of overhead
    /// compared to the more streamlined [`ByteParser`] it is based on.
    ///
    /// # Panics
    ///
    /// This method will panic if the interior call to [`try_decode`]
    /// returns an `Err(_)` value.
    ///
    /// [`MemoParser`]: crate::parse::memoparser::MemoParser
    /// [`ByteParser`]: crate::parse::memoparser::ByteParser
    fn decode_memo<U>(inp: U) -> Self
        where
            Self: Sized,
            U: TryIntoParser<crate::parse::memoparser::MemoParser>,
            error::DecodeError: From<U::Error>
    {
        Self::try_decode(inp).unwrap_or_else(|_| {
            panic!(
                "<{} as Decode>::decode_memo: unable to parse value (DecodeError encountered)",
                std::any::type_name::<Self>()
            )
        })
    }

    /// Decodes a value of type `Self` from a value `input` of the generic
    /// type `U: TryIntoParser`, using [`ByteParser`] as the
    /// `Parser` type internally.
    ///
    /// This is a more streamlined alternative to [`decode_memo`], which
    /// is less performant but includes more debugging information upon failure.
    ///
    /// # Panics
    ///
    /// This method will panic if the interior call to [`try_decode`]
    /// returns an `Err(_)` value.
    ///
    /// [`ByteParser`]: crate::parse::memoparser::ByteParser
    fn decode<U>(inp: U) -> Self
        where Self: Sized, U: TryIntoParser, error::DecodeError: From<U::Error>
    {
        Self::try_decode(inp).unwrap_or_else(|err| {
            panic!(
                "<{} as Decode>::decode encountered error: {:?}",
                std::any::type_name::<Self>(),
                err
            )
        })
    }
}

impl Encode for Vec<u8> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        buf.push_all(self) + crate::resolve_zero!(buf)
    }

    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        buf.extend_from_slice(self.as_slice())
    }

    fn encode<U: Target>(&self) -> U {
        let mut tgt: U = U::create();
        let _n = self.write_to(&mut tgt);
        debug_assert_eq!(_n, self.len());
        tgt
    }

    fn to_bytes(&self) -> Vec<u8> {
        self.clone()
    }
}

impl Decode for Vec<u8> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        p.take_dynamic(p.remainder())
    }
}

impl Encode for String {
    fn write_to<W: Target>(&self, buf: &mut W) -> usize {
        buf.push_all(self.as_bytes()) + crate::resolve_zero!(buf)
    }
}

impl Decode for String {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        let buf: Vec<u8> = p.take_dynamic(p.remainder())?;

        Ok(String::from_utf8_lossy(&buf).into_owned())
    }
}

impl<T: Encode> Encode for Option<T> {
    fn write_to<U: Target>(&self, buf: &mut U) -> usize {
        (match self {
            Some(val) => buf.push_one(0xff) + val.write_to(buf),
            None => buf.push_one(0x00),
        }) + crate::resolve_zero!(buf)
    }
}

impl<T: Decode> Decode for Option<T> {
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self> {
        match p.take_tagword::<Option<T>, _, _>([0x00u8, 0xff])? {
            0xff => Ok(Some(T::parse(p)?)),
            0x00 => Ok(None),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{ Builder, Encode, StrictBuilder };

    #[test]
    fn check() {
        assert_eq!(b"foo".to_vec().encode::<StrictBuilder>().into_bin().unwrap(), "foo");
    }
}