//! Core of the binary-conversion API
//!
//! This module provides the primary functionality of the runtime, the trait definitions
//! for `Encode` and `Decode`, which are motivationally equivalent to the `Serialize` and `Deserialize`
//! traits defined in `serde`, for example.
//!
//! While a great deal of the underlying machinery of this crate is subject to customization
//! by end-users, such as the definition of custom `Parser` and `Target` trait implementors,
//! `Encode` and `Decode` form the core of this library, and substituting them wholesale would
//! be morally equivalent to using a different runtime library.
//!
//! While the internal implementations may change, this module exposes a comparatively stable API,
//! as the structures of `Encode` and `Decode` cannot be altered without drastic changes not only to the
//! remainder of the library itself, but also the abstract model, and generative logic used in the
//! `codec_generator` that this library is designed in tandem with.
//!
//! The sub-module [`len`], which defines `Estimable` and its refinements, is also
//! a major feature of the runtime, but to a far lesser extent; it is possible to eliminate Estimable
//! entirely and code around it in certain places without much side-effect, while Encode and Decode
//! cannot be easily deprecated or phased out.
//!
//! An additional submodule, [`target`], offers an abstraction around [`std::io::Write`], namely the
//! [`target::Target`] trait. This is the dual to [`crate::parse::Parser`], acting as the generic
//! bound for serialization in the [`Decode::write_to`] method among others.
//!
//! Derive macros for Encode, Decode, and even Estimable are provided in the sub-crates `encode_derive`,
//! `decode_derive`, and `estimable_derive`, which are only relevant within the context of this runtime.

use crate::parse::{ParseResult, Parser, TryIntoParser};

use self::target::Target;

pub mod error;
pub mod len;
pub mod target;

pub use error::DecodeResult;

#[macro_export]
macro_rules! write_all_to {
    ( $($x:expr),* $(,)? => $tgt:expr ) => {
        { $( $x.write_to($tgt) + )* $crate::conv::target::Target::resolve_zero($tgt) }
    };
}

/// Trait providing methods for serializing values of a certain type
///
/// This trait should only be implemented on types for which there is
/// a standard binary encoding scheme within the `data-encoding` OCaml library,
///
/// Implementations are defined by one required method, [`write_to`]:
///   * The `write_to` method writes the received object (generic, bound by
///     [`Target`]) to the specified buffer, returning the number of bytes that
///     were written. Unlike [`std::io::Write::write`], it is infallible, though
///     that detail may change in later versions.
///
/// If the implementing type can implement the remaining methods more efficiently than
/// the default implementations allow for, it is recommended to override them, provided
/// the operational semantics are left unchanged.
///
/// [`Target`]: crate::conv::target::Target
pub trait Encode {
    /// Appends the serialized bytes of `self` to `buf`
    ///
    /// The natural definition of this method is structurally inductive on the
    /// physical or virtual fields of the type in question, in conformance with
    /// the serialization format defined by `data-encoding`.
    fn write_to<U: Target>(&self, buf: &mut U) -> usize;

    /// Appends the serialzed bytes of `self` to `buf`
    ///
    /// This method is a specialized variant of [`write_to`] for `Vec<u8>`
    /// targets.
    fn write_to_vec(&self, buf: &mut Vec<u8>) {
        let _ = self.write_to(buf);
    }

    /// Constructs and returns a buffer of type `U` that has been populated with the
    /// serialized bytes of `self`
    fn encode<U: Target>(&self) -> U {
        let mut buf: U = U::create();
        let _ = self.write_to::<U>(&mut buf);
        buf
    }

    /// Constructs and returns a `Vec<u8>` containing the serialized bytes of `self`
    fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        self.write_to_vec(&mut buf);
        buf
    }
}

/// Extension trait for `Encode` with serialization-length oracles
///
/// This trait defines additional methods on an `Encode` type, which allow
/// for zero-allocation computations of the number of bytes in the serialization
/// of a value, as well as a zero-realloc version of [`Encode::to_bytes`] based
/// on this count.
pub trait EncodeLength: Encode {
    /// Computes, without allocation, the number of bytes in the serialized
    /// form of `self`, based on the implementation of [`Encode::write_to`].
    ///
    /// The default implementation of this method uses a target of [`ByteCounter`]
    /// to discard the bytes that would be written by [`write_to`], preserving only
    /// the return-value, equal to the number of bytes that were 'written' in this
    /// manner.
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
/// # use ::rust_runtime::parse::{Parser, ParseResult, byteparser::ByteParser};
/// use rust_runtime::Decode
/// use rust_runtime::{VPadded, Bytes, Sequence, seq};
///
///
/// pub struct MyTypeElem {
///     is_valid: bool,
///     id: u8,
/// }
///
///
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
    fn parse<P: Parser>(p: &mut P) -> ParseResult<Self>
    where
        Self: Sized;

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
    where
        Self: Sized,
        P: Parser,
        U: TryIntoParser<P>,
        error::DecodeError: From<U::Error>
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
    where
        Self: Sized,
        U: TryIntoParser,
        error::DecodeError: From<U::Error>
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

        Ok(String::from_utf8(buf)?)
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
    use crate::{Builder, Encode, StrictBuilder};

    #[test]
    fn check() {
        assert_eq!(
            (b"foo")
                .to_vec()
                .encode::<StrictBuilder>()
                .into_bin()
                .unwrap(),
            "foo"
        );
    }
}
