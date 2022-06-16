//! Error types used to report failure in low-level parsing
//!
//! This module contains a hierarchy of types representing specific
//! classes of error that may arise as a result of calls to
//! [`Parser`](../parse/trait.Parser.html) methods. Some of these
//! may also be returned by lower-level operations that specific
//! implementors of `Parser` rely on.
//!
//! # Layout
//!
//! This module defines the primary type `ParseError` and the alias
//! `ParseResult<T>`; it additionally defines various type-level refinements of
//! `ParseError`, grouped according to similar provenance or nature.

use std::{
    convert::Infallible,
    fmt::{Display, Formatter, Result},
    string::FromUtf8Error,
};

use crate::error::{BoundsError, ConstraintError};

/// Any error that may be encountered within `Parser`-related code
///
///
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    /// Error class encountered when opening, closing, or checking context windows.
    WindowError(WindowError),
    /// Error class encountered when internal invariants or preconditions are violated
    InternalError(InternalError),
    /// Error class encountered when low-level parsing is successful but
    /// the resultant raw value cannot be converted into a legal value of
    /// a post-parse type
    ///
    /// This class of error is the only one that can occur even after the correspondign
    /// parse operation is successful
    ExternalError(ExternalError),
    /// Error class encountered when low-level parsing is unsuccessful due
    /// to a failure of expectation in terms of the binary-lexical contents
    /// of the buffer.
    ///
    /// This includes invalid tag-words, illegal values for bytes intended to
    /// represent booleans, and failure of self-terminating values to terminate
    /// before reaching a frame-limit.
    TokenError(TokenError),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ParseError::WindowError(err) => {
                write!(f, "Context-window error: {}", err)
            }
            ParseError::InternalError(err) => {
                write!(f, "Internal error: {}", err)
            }
            ParseError::ExternalError(err) => {
                write!(f, "External error: {}", err)
            }
            ParseError::TokenError(err) => {
                write!(f, "Token error: {}", err)
            }
        }
    }
}

impl From<Infallible> for ParseError {
    fn from(_: Infallible) -> Self {
        unreachable!()
    }
}

/// Type alias for Result with an error type of [`ParseError`]
///
/// Most `Parser` methods, some lower-level internal methods
/// used in parsing, and certain `Decode` methods have a return
/// type of `ParseResult<T>` for various `T`
pub type ParseResult<T> = std::result::Result<T, ParseError>;

/// Errors related to context-windows
///
/// opening, closing, and adhering to context-windows for `Parser`
/// types.
///
/// Certain low-level state-manipulation operations defined in the
/// private module `internal` may also produce errors of this type,
/// although these may be wrapped inside of `WindowErrorKind` may
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WindowError {
    /// Error case when a method that attempts to consume some number
    /// of bytes from the buffer of a `Parser` would violate either
    /// the absolute end-of-buffer or the current context-window in
    /// doing so.
    ///
    /// The distinction between absolute overrun and contextual
    /// overrun is not made at this level, as buffers may not
    /// always be able to tell the difference synchronously.
    ConsumeWouldExceedLimit {
        offset: usize,
        requested: usize,
        limit: usize,
    },
    /// Error case when a method call attempts to open a window
    /// that, if created, would extend beyond the final byte in
    /// the parse-buffer.
    ///
    /// Note that this case can be a fallthrough, and that if a parse-window
    /// happens to exist at the same time, [`OpenWouldExceedWindow`] may
    /// be the reported error.
    OpenWouldExceedBuffer { bytes_left: usize, request: usize },
    /// Error case when a method call attempts to open a window
    /// that, if created, would be wider than the narrowest
    /// open context-window.
    ///
    /// Note that this error may be reported in cases where the method call
    /// would fail regardless, such as when the requested width would also
    /// exceed successive open windows, or even the entire parse-buffer itself.
    OpenWouldExceedWindow { limit: usize, request: usize },
    /// Error case when a method call attempts to close the narrowest open
    /// context-window but there are unconsumed bytes remaining within said
    /// window.
    CloseWithResidue { residual: usize },
    /// Error case when a method call attempts to close the narrowest open
    /// context-window, but there are no open context-windows to begin with.
    CloseWithoutWindow,
    /// Generic error case where the current offset of a Parser exceeds the bounds
    /// of the narrowest open context-window.
    ///
    /// This case is never expected to be reached, but it is included nonetheless.
    /// It is a critical error in the implementation of a parser if this error is
    /// ever reported.
    OffsetOverflow { excess: usize },
}

impl From<WindowError> for ParseError {
    fn from(err: WindowError) -> Self {
        Self::WindowError(err)
    }
}

impl Display for WindowError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match *self {
            WindowError::ConsumeWouldExceedLimit {
                limit,
                offset,
                requested,
            } => {
                write!(
                    f,
                    "cannot increment offset by {} bytes (currently at byte {} out of limit {})",
                    requested, offset, limit
                )
            }
            WindowError::OpenWouldExceedBuffer {
                bytes_left,
                request,
            } => {
                if bytes_left == 0 {
                    write!(
                        f,
                        "cannot open {}-byte context window: parse-buffer has been fully consumed",
                        request
                    )
                } else {
                    write!(f, "cannot open {}-byte context window: parse-buffer has only {} bytes remaining", request, bytes_left)
                }
            }
            WindowError::OpenWouldExceedWindow { limit, request } => {
                write!(
                    f,
                    "Cannot open {}-byte context window: wider than current window ({} bytes)",
                    request, limit
                )
            }
            WindowError::CloseWithResidue { residual } => {
                write!(
                    f,
                    "cannot close context window with {} residual bytes",
                    residual
                )
            }
            WindowError::CloseWithoutWindow => write!(f, "no context window to close"),
            WindowError::OffsetOverflow { excess } => {
                write!(
                    f,
                    "BUG: detected an offset that exceeds the current limit by {} bytes",
                    excess
                )
            }
        }
    }
}

/// Errors arising from unexpected tokens in the buffer
///
/// Includes tag errors, boolean value errors, and non-termination
/// of supposedly self-terminating values
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenError {
    InvalidBoolean(u8),
    /// Byte parsed could not be interpreted as a valid discriminant for an enumerated type
    /// with one-byte tag
    InvalidTagU8(TagError<u8>),
    /// Byte parsed could not be interpreted as a valid discriminant for an enumerated type
    /// with two-byte tag
    InvalidTagU16(TagError<u16>),
    /// Byte parsed could not be interpreted as a valid discriminant for an enumerated type
    /// with four-byte tag
    InvalidTagU30(TagError<u32>),
    /// Supposedly self-terminating byte-sequence failed to terminate before reaching end of buffer
    NonTerminating(Vec<u8>),
    /// Implicitly NIL-valued padding contained non-NIL byte
    NonNullPaddingByte {
        padding: Vec<u8>,
        invalid: usize,
    },
}

impl From<TokenError> for ParseError {
    fn from(tok_e: TokenError) -> Self {
        Self::TokenError(tok_e)
    }
}

impl Display for TokenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Self::InvalidBoolean(byte) => {
                write!(f, "invalid boolean encoding 0x{byte:02x}")
            }
            Self::InvalidTagU8(err) => {
                write!(f, "invalid tag: {}", err)
            }
            Self::InvalidTagU16(err) => {
                write!(f, "invalid tag: {}", err)
            }
            Self::InvalidTagU30(err) => {
                write!(f, "invalid tag: {}", err)
            }
            Self::NonTerminating(buf) => {
                write!(
                    f,
                    "self-terminating element failed to terminate within bounding context: `{}`",
                    crate::util::hex_of_bytes(buf)
                )
            }
            Self::NonNullPaddingByte { padding, invalid } => {
                if let (valid, &[nonnull, ref tail @ ..]) = padding.split_at(*invalid) {
                    write!(f, "non-null byte found in padding: ")?;
                    crate::util::write_all_hex(valid, f)?;
                    write!(f, ">{nonnull:02x}<")?;
                    crate::util::write_all_hex(tail, f)
                } else {
                    unreachable!()
                }
            }
        }
    }
}

/// Implementation-internal errors
///
/// This error class represents certain 'impossible' cases, which signify
/// an implementation bug in either the implementation of a `Parser` type,
/// or a violation of a precondition for calling certain `Parser` methods.
///
/// Such cases do not merely indicate that the caller has failed to guarantee
/// a required property, it indicates that something deeply wrong has happened.
///
/// It is possible that this type of error will be deprecated, and the logic
/// that produces values of this type may instead use `unreachable!()`,
/// or `assert!`-like mechanisms that issue panics when things go wrong.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InternalError {
    ConsumeLengthMismatch { expected: usize, actual: usize },
    SliceCoerceFailure,
    NoValidTags,
}

impl From<InternalError> for ParseError {
    fn from(ierr: InternalError) -> Self {
        Self::InternalError(ierr)
    }
}
/// Converts a borrowed byte-slice into an owned byte-array
///
/// Returns a [`ParseError`] corresponding to the reason for
/// failure if this conversion cannot be performed for any reason.
///
/// This error is guaranteed to be an `InternalError`.
pub(crate) fn coerce_slice<const N: usize>(bytes: &'_ [u8]) -> ParseResult<[u8; N]> {
    let actual = bytes.len();
    if actual != N {
        Err((InternalError::ConsumeLengthMismatch {
            expected: N,
            actual,
        })
        .into())
    } else {
        match <[u8; N] as std::convert::TryFrom<&'_ [u8]>>::try_from(bytes) {
            Ok(arr) => Ok(arr),
            Err(_err) => Err(InternalError::SliceCoerceFailure.into()),
        }
    }
}

impl Display for InternalError {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            InternalError::ConsumeLengthMismatch { expected, actual } => {
                write!(
                    f,
                    "bug: consume({}) returned slice of length {}",
                    expected, actual
                )
            }
            InternalError::SliceCoerceFailure => {
                write!(
                    f,
                    "bug: failed to coerce from byte-slice to fixed-length array"
                )
            }
            InternalError::NoValidTags => {
                write!(
                    f,
                    "bug: cannot parse discriminant of enum with no specified valid values"
                )
            }
        }
    }
}

/// Enumerated type representing contextually invalid results obtained from otherwise
/// succesfully executed method calls to a Parser object. These typically indicate that
/// the actual byte content of the buffer differs from the byte content that is considered
/// valid in the context imposed by a particular parse method call or combination thereof.
#[derive(Debug, Clone, PartialEq)]
pub enum ExternalError {
    /// Error scenario in which a coercion from `&[u8]` to `String` performed on the result
    /// of a `consume` operation could not be performed for the specified reason (`FromUtf8Error`).
    UncoercableString(FromUtf8Error),
    /// Error scenario in which an integral value parsed from the buffer happened to fall outside
    /// of the valid range of a RangedInt type.
    IntRangeViolation(BoundsError<i64>),
    /// Error scenario in which a double-precision IEEE float parsed from the buffer happened to fall
    /// outside of the valid range of a RangedFloat type.
    FloatRangeViolation(BoundsError<f64>),
    /// Error scenario in which a trivial type-conversion could not be performed without implicitly
    /// violating a type-level (schema-level) constraint in the target type.
    ConstraintViolation(ConstraintError),
}

impl<T> From<T> for ParseError
where
    ExternalError: From<T>,
{
    fn from(err: T) -> Self {
        ParseError::ExternalError(ExternalError::from(err))
    }
}

impl From<FromUtf8Error> for ExternalError {
    fn from(err: FromUtf8Error) -> Self {
        Self::UncoercableString(err)
    }
}

impl From<BoundsError<i64>> for ExternalError {
    fn from(err: BoundsError<i64>) -> Self {
        Self::IntRangeViolation(err)
    }
}

impl From<BoundsError<f64>> for ExternalError {
    fn from(err: BoundsError<f64>) -> Self {
        Self::FloatRangeViolation(err)
    }
}

impl From<ConstraintError> for ExternalError {
    fn from(err: ConstraintError) -> Self {
        Self::ConstraintViolation(err)
    }
}

impl Display for ExternalError {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            ExternalError::UncoercableString(err) => {
                write!(
                    f,
                    "parsed byte-array could not be coerced to String: {}",
                    err
                )
            }
            ExternalError::IntRangeViolation(x) => {
                write!(f, "{}", x)
            }
            ExternalError::FloatRangeViolation(x) => {
                write!(f, "{}", x)
            }
            ExternalError::ConstraintViolation(x) => {
                write!(f, "{}", x)
            }
        }
    }
}

/// Sealed trait on types used for enum tags
///
/// Marker trait on [`u8`], [`u16`], and [`u32`] (representing [`u30`][uthirty])
/// to be used as trait bounds on the generic `T` in `TagError<T>`.
///
/// Defines a `promote` method that lifts from `TagError<Self>` to `ParseError`
///
/// This trait is sealed, meaning it cannot be implemented by on any downstream
/// types.
///
/// [uthirty]: ../../int/type.u30.html
pub trait TagType
where
    Self: Sized
        + std::fmt::Debug
        + std::fmt::Display
        + std::fmt::LowerHex
        + PartialEq
        + Copy
        + private::Sealed,
{
    /// Lifts a `TagError<Self>` into a [`ParseError`] by wrapping
    /// it in the appropriate constructors
    fn promote(val: TagError<Self>) -> ParseError;
}

impl TagType for u8 {
    /// Lifts a `TagError<u8>` into a [`ParseError`] by wrapping
    /// it in the appropriate constructors
    fn promote(val: TagError<Self>) -> ParseError {
        TokenError::InvalidTagU8(val).into()
    }
}

impl TagType for u16 {
    /// Lifts a `TagError<u16>` into a [`ParseError`] by wrapping
    /// it in the appropriate constructors
    fn promote(val: TagError<Self>) -> ParseError {
        TokenError::InvalidTagU16(val).into()
    }
}

impl TagType for u32 {
    /// Lifts a `TagError<u32>` into a [`ParseError`] by wrapping
    /// it in the appropriate constructors
    fn promote(val: TagError<Self>) -> ParseError {
        TokenError::InvalidTagU30(val).into()
    }
}

/// General-purpose trait for abstracting tag-value validation
///
/// This is used to allow for a more flexible API for the
/// `Parser` method [`take_tagword`](crate::parse::Parser::take_tagword).
///
/// This trait encapsulates the common behavior of determining whether
/// a given value of type `U` is a member of the closed set of valid
/// discriminants for an arbitrary schema ADT. This includes both
/// C-Style and Data-enums.
///
/// The primary implementors of this trait are array-like collections
/// over all valid discriminant values, either as constant-length
/// arrays, slices, or vectors.
///
/// As needed, additional implementations may be added for more varied
/// validators, such as collection types with better-than-`O(n)`
/// membership operations.
pub trait TagValidator<U>
where
    U: TagType,
{
    /// Returns `true` if and only if `raw` is a valid tag.
    fn is_valid(&self, raw: U) -> bool;

    /// Returns `true` if and only if there are no valid tags.
    ///
    /// Note that this is never the desired state for a `TagValidator`
    /// to be in, and is used primarily for accurate error-reporting
    /// upon rejection of a candidate value during parsing.
    fn has_valid(&self) -> bool;

    /// Consumes `self` and returns a vector containing all of the
    /// values that are considered valid.
    ///
    /// This method is called only to provide more informative error
    /// values upon rejection of a parsed candidate tag-value. As a
    /// result, it is not performance-critical, and is not even required
    /// to succeed, as long as it does not panic.
    ///
    /// A common transparent way to indicate the impossibility of this
    /// request, such as when the implementor is a closure type, or
    /// similarly does not offer any direct means of introspecting the
    /// tags it would consider valid, would be to return an empty vector.
    fn into_valid(self) -> Vec<U>;
}

pub mod impls {
    use super::TagValidator;

    #[inline]
    #[must_use]
    pub fn contains_u8(needle: u8, haystack: &[u8]) -> bool {
        haystack.contains(&needle)
    }
    #[inline]
    #[must_use]
    pub fn contains_u16(needle: u16, haystack: &[u16]) -> bool {
        haystack.contains(&needle)
    }
    #[inline]
    #[must_use]
    pub fn contains_u32(needle: u32, haystack: &[u32]) -> bool {
        haystack.contains(&needle)
    }

    macro_rules! impl_container_tagvalidator {
        ( $tagtyp:ty, $contains:ident ) => {
            impl<const N: usize> TagValidator<$tagtyp> for [$tagtyp; N] {
                fn is_valid(&self, raw: $tagtyp) -> bool {
                    $contains(raw, &*self)
                }

                fn has_valid(&self) -> bool {
                    N > 0
                }

                fn into_valid(self) -> Vec<$tagtyp> {
                    self.to_vec()
                }
            }

            impl<const N: usize> TagValidator<$tagtyp> for &'_ [$tagtyp; N] {
                fn is_valid(&self, raw: $tagtyp) -> bool {
                    $contains(raw, *self)
                }

                fn has_valid(&self) -> bool {
                    N > 0
                }

                fn into_valid(self) -> Vec<$tagtyp> {
                    self.to_vec()
                }
            }

            impl TagValidator<$tagtyp> for &'_ [$tagtyp] {
                fn is_valid(&self, raw: $tagtyp) -> bool {
                    $contains(raw, self)
                }

                fn has_valid(&self) -> bool {
                    self.len() > 0
                }

                fn into_valid(self) -> Vec<$tagtyp> {
                    self.to_vec()
                }
            }

            impl TagValidator<$tagtyp> for Vec<$tagtyp> {
                fn is_valid(&self, raw: $tagtyp) -> bool {
                    $contains(raw, self.as_slice())
                }

                fn has_valid(&self) -> bool {
                    self.len() > 0
                }

                fn into_valid(self) -> Vec<$tagtyp> {
                    self
                }
            }

            impl TagValidator<$tagtyp> for &'_ Vec<$tagtyp> {
                fn is_valid(&self, raw: $tagtyp) -> bool {
                    $contains(raw, self.as_slice())
                }

                fn has_valid(&self) -> bool {
                    self.len() > 0
                }

                fn into_valid(self) -> Vec<$tagtyp> {
                    self.clone()
                }
            }
        };
    }

    impl_container_tagvalidator!(u8, contains_u8);
    impl_container_tagvalidator!(u16, contains_u16);
    impl_container_tagvalidator!(u32, contains_u32);
}

mod private {
    pub trait Sealed {}

    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
}

/// Error representing invalid enum-tag values
///
/// Although this type is technically generic over any `T`, only
/// `u8`, `u16`, and `u32` should be used for this type.
///
/// This condition is partially enforced by the trait bound of `T: TagType`,
/// which, as an unsafe trait, cannot be implemented on other types in Safe
/// Rust.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagError<T: TagType> {
    actual: T,
    for_type: &'static str,
    expected: Option<Vec<T>>,
}

impl<T: TagType> From<TagError<T>> for ParseError {
    fn from(val: TagError<T>) -> Self {
        <T as TagType>::promote(val)
    }
}

impl<T> TagError<T>
where
    T: Into<TagError<T>> + TagType,
{
    pub fn new(actual: T, for_type: &'static str, expected: Option<Vec<T>>) -> Self {
        Self {
            actual,
            for_type,
            expected,
        }
    }
}

impl<T: TagType> From<T> for TagError<T> {
    fn from(actual: T) -> Self {
        Self {
            actual,
            for_type: "<unknown>",
            expected: None,
        }
    }
}

impl<T> Display for TagError<T>
where
    T: TagType,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(
            f,
            "unexpected discriminant {:#0width$x} for enum-type {}",
            &self.actual,
            self.for_type,
            width = std::mem::size_of::<T>() * 2
        )
    }
}

macro_rules! mk_error {
    ( $( $et:ty ),+ $(,)? ) => {
        $( impl std::error::Error for $et {} )+
    };
}

mk_error! {
    ParseError,
    WindowError,
    InternalError,
    TokenError,
    ExternalError,
    TagError<u8>,
    TagError<u16>,
    TagError<u32>,
}
