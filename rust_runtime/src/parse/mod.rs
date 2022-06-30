//! Custom parsing model with byte-level precision
//!
//! This module, along with its submodules, provides the fundamental
//! definitions related to the abstract task of processing raw sequences
//! of binary data into the low-level fragments at the leaf nodes of
//! an arbitrarily complex user-defined type.
//!
//! For type-aware parsing, in other words, parsing user-defined types
//! directly rather than as an unstructured sequence of primitives,
//! see the [`Decode`](../conv/trait.Decode.html) trait, which is a
//! high-level interface built almost entirely around the definitions
//! contained within this module.
//!
//! # Layout
//!
//! The top-level of this module defines the [`Parser`] trait, along with
//! the utility trait [`ToParser<P>`] which facilitates the generic instantiation
//! of various parser-types from a variety of source types.
//! There are four general sub-modules that contain types, functions,
//! and trait implementations that are associated directly with the
//! `Parser` trait:
//!   * `error` defines the hierachy of error cases that can be encountered and returned when something goes wrong
//!     during a call to a `Parser` method, either due to mis-use or implementation bugs.
//!   * `hexstring` defines user-facing tools for guaranteeing the correct interpretation of bytestrings
//!     and character-strings that should be interpreted as hexadecimal encodings of binary, rather than
//!     raw binary sequences.
//!   * `bytes` defines the structures used as the binary buffers within the
//!     implementing types of `Parser` defined within this crate.
//!   * `cleanup` defines a framework for gracefully discarding `Parser` objects once they are no longer
//!     needed, which additionally checks that the `Parser` has been left in a fully-processed state.
//!
//! Additionally, three implementating types of `Parser` are packaged in accordingly-named modules:
//! `byteparser` for `ByteParser`, `sliceparser` for `SliceParser`, and `memoparser` for `MemoParser`.
//!
//! See the module-level documentation of the sub-modules for more details.

pub mod error;

pub use error::ParseResult;
use error::{InternalError, ParseError, TagError};
use std::convert::{TryFrom, TryInto};

/// # Parser
///
///   This trait is an abstraction over types respresenting a stateful
///   parse-object, with default implementations for a variety of monomorphic
///   `get_*` functions, as well as query operations on the internal state,
///   and state-mutational functions that operate on *context-windows*.
///
///  ## Model
///
///  While the implementing types are largely free to define their own
///  operational semantics for the required methods of this function, the
///  intensional semantics are as follows:
///
///  * The Parser-object is constructed over an immutable byte-buffer.
///  * All parsing is done in a non-backtracking, zero-lookahead fashion; a byte in the buffer
///    can only be viewed by consuming it, and only after all preceding indices in the buffer
///    have been consumed; after a byte is consumed, it cannot be consumed again.
///  * A *context-window*, or a bounded contiguous view of a section of the buffer,
///    may be constructed. While a context-window exists, any bytes beyond its upper bound
///    are protected and cannot be consumed by any Parser method until that
///    context window is lifted. A context-window can only be lifted by calling
///    [enforce_target] when all bytes within the window have been consumed.
///
/// ## Context-Windows
///
/// In order to facilitate bounds-setting and bounds-checking for dynamically sized elements with length prefixes,
/// `Parser` uses a model of *context windows*, which are conceptually (though not necessarily implementationally) a stack
/// of target offsets, which may in fact be hard lower bounds on remainding-buffer-length in the case of slice-based parsers, or fixed values
/// of the mutating parse-head for buffer-based implementations such as [ByteParser].
///
/// The following properties should be respected by each implementation of the `Parser` trait:
///
/// * A fresh `p : impl Parser` object should have `p.offset() == 0` and `p.len()` equal to the length of the parse-buffer
/// * `self.remainder() := self.len() - self.offset()` is the largest possible `n` for which `self.consume(n)` returns an `Ok(_)` value, which should also be the largest possible `n` for which `self.set_fit(n)` succeeds. Both should fail for any greater values of `n`, either through `Err(_)` returns or panics.
/// * The value of ``self.remainder()` before and after a call to `self.consume(n)` should represent a decrease by `n` if the consume call is an `Ok(_)` value, or remain unchanged if it is an `Err(_)` value.
/// * `self.set_fit(m)` should fail whenever `self.remainder() < m`, and succeed otherwise
/// * Immediately after a successful call of `self.set_fit(n)`, `self.remainder()` should return `n`
/// * `self.test_target()` should return `true` if and only if `self.offset() == self.len()` holds with at least one context window present
/// * `self.enforce_target()` should remove the most recently set target if `self.test_target()` would return true, and panic otherwise
pub trait Parser {
    /// Buffer type a new `Parser` object can be safely and infallibly
    /// instantiated from a value of.
    ///
    /// Typically will be one of [`buffer::VecBuffer`] or [`buffer::SliceBuffer<'a>`],
    /// but may have other values for more exotic or specialized Parser types.
    type Buffer;

    /// Constructs an initialized `Parser` value over a buffer
    fn from_buffer(buf: Self::Buffer) -> Self;

    /// Computes the length of the current view of the Parser's buffer.
    ///
    /// Decrements in the shrinking-slice model, and remains invariant modulo context-window
    /// manipulation in the buffer-with-offset model
    fn view_len(&self) -> usize;

    /// Computes the current value of the offset into the Parser's buffer.
    ///
    /// This should either be invariant, or increase by the number of bytes consumed
    /// by any method that returns bytes from the buffer.
    fn offset(&self) -> usize;

    /// Computes the remaining number of bytes that can be safely consumed in the current context.
    ///
    /// Even if it can be implemented directly,
    /// this should always return the same value as computing `self.len() - self.offset()`
    #[inline]
    fn remainder(&self) -> usize {
        self.view_len() - self.offset()
    }

    /// Consumes and returns a single byte from the current offset position
    /// in the buffer.
    ///
    /// This method should be functionally equivalent to [`consume`] call of
    /// length `1`, aside from the different return types.
    fn consume_byte(&mut self) -> ParseResult<u8>;

    /// Attempt to consume and return a slice of length `nbytes`,
    /// starting from the first unconsumed byte in the buffer.
    ///
    /// If either the absolute bounds of the buffer, or context-window limits
    /// would be violated by such an attempt, no bytes should be consumed,
    /// although it is not considered unsound to mutate the Parser state as long
    /// as the error is correctly presented.
    ///
    /// # Invariants
    ///
    /// This method **MUST** return `Ok(s)` when and only when no bounds or
    /// limits were violated, and in such cases, `s.len()` must be equal to the
    /// requested length `nbytes`. Failure to guarantee this is an
    /// implementation bug.
    fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]>;

    /// Creates a new context-window that permits exactly `n` more bytes to be consumed before
    /// subsequent consume operations fail.
    ///
    /// `self.set_fit(m)` should fail whenever `self.remainder() < m`, and succeed otherwise.
    ///
    /// Immediately after a successful call of `self.set_fit(n)`, `self.remainder()` should equal `n`.
    fn set_fit(&mut self, n: usize) -> ParseResult<()>;

    /// Tests to see whether there there is any context window open, and whether it can be safely closed
    /// without consuming any more bytes.
    ///
    /// It should return true if and only if `self.reminder() == 0` and there is at least one unclosed context window.
    fn test_target(&mut self) -> ParseResult<bool>;

    /// Attempt to close the current context-window.
    ///
    /// Returns `Ok(())` if the target was successfully enforced, and the corresponding
    /// open context-window was closed.
    ///
    /// # Errors
    ///
    /// If there are no open context-windows when this method is called, this
    /// method must always return
    /// `Err(Window(WindowError::CloseWithoutWindow))`.
    ///
    /// If there are any unconsumed bytes in the current context-window when
    /// this method is called, this method must always return
    /// `Err(Window(WindowError::CloseWithResidue))`
    ///
    /// Otherwise, the only acceptable error to return is
    /// `Err(Window(WindowError::OffsetOverflow))`, although it is expected that
    /// this case should never occur in a sound implementation.
    fn enforce_target(&mut self) -> ParseResult<()>;

    /// Consumes `N` bytes and returns them in array-form
    ///
    /// # Errors
    ///
    /// This method will propogate any errors from the internal call
    /// to [`consume`], and should not otherwise return any errors.
    ///
    /// Though doing so would be indicative of an implementatin bug, it is
    /// also technically possible for this method to return
    /// `Err(External(ExternalError::SliceCoerceFailure(_)))`
    fn consume_arr<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
        error::coerce_slice(self.consume(N)?)
    }

    /// Consumes one byte and returns it as a `u8` value
    #[inline]
    fn take_u8(&mut self) -> ParseResult<u8> {
        self.consume_byte()
    }

    /// Consumes one byte and returns it as an `i8` value.
    ///
    /// Equivalent to `self.take_u8().map(|x| x as i8)`
    #[inline]
    fn take_i8(&mut self) -> ParseResult<i8> {
        Ok(self.consume_byte()? as i8)
    }

    /// Consumes two bytes and returns the corresponding `u16` value
    ///
    /// As with all fixed-width multi-byte numeric `take_X` methods,
    /// this method performs an implicitly big-endian conversion with
    /// respect to the individual bytes consumed.
    #[inline]
    fn take_u16(&mut self) -> ParseResult<u16> {
        self.consume_arr::<2>().map(u16::from_be_bytes)
    }

    /// Consumes two bytes and returns the corresponding `i16` value
    ///
    /// As with all fixed-width numeric `take_X` methods, this method performs
    /// an implicitly big-endian conversion with respect to the individual bytes
    /// consumed.
    #[inline]
    fn take_i16(&mut self) -> ParseResult<i16> {
        self.consume_arr::<2>().map(i16::from_be_bytes)
    }

    /// Consumes four bytes and returns the corresponding `u32` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// big-endian conversion from `[u8; _]` to the multi-byte integral type.
    #[inline]
    fn take_u32(&mut self) -> ParseResult<u32> {
        self.consume_arr::<4>().map(u32::from_be_bytes)
    }

    /// Consumes four bytes and returns the corresponding `i32` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// big-endian conversion from `[u8; _]` to the multi-byte integral type.
    #[inline]
    fn take_i32(&mut self) -> ParseResult<i32> {
        self.consume_arr::<4>().map(i32::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `u64` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// big-endian conversion from `[u8; _]` to the multi-byte integral type.
    #[inline]
    fn take_u64(&mut self) -> ParseResult<u64> {
        self.consume_arr::<8>().map(u64::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `f64` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// big-endian conversion from `[u8; _]` to the multi-byte integral type.
    #[inline]
    fn take_f64(&mut self) -> ParseResult<f64> {
        self.consume_arr::<8>().map(f64::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `i64` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// big-endian conversion from `[u8; _]` to the multi-byte integral type.
    #[inline]
    fn take_i64(&mut self) -> ParseResult<i64> {
        self.consume_arr::<8>().map(i64::from_be_bytes)
    }

    /// Consumes a single byte and returns the boolean value it represents
    ///
    /// According to the binary schema used in `data-encoding`,
    /// the only valid boolean encodings are `0xff` for `true`
    /// and `0x00` for `false`.
    ///
    /// # Errors
    ///
    /// Will propogate any error returned by the internal consume method call.
    ///
    /// In addition, will return a
    /// [`TokenError::InvalidBoolean`](crate::parse::error::TokenError::InvalidBoolean)
    /// the invalid byte, wrapped suitably as a `ParseError`
    #[inline]
    fn take_bool(&mut self) -> ParseResult<bool> {
        match self.consume_byte()? {
            0xff => Ok(true),
            0x00 => Ok(false),
            byte => Err(ParseError::Token(TokenError::InvalidBoolean(byte))),
        }
    }

    /// Parses a `u8`, `u16`, or `u32` (determined by the second generic parameter `U`)
    /// and verifies that it is a valid discriminant for the intended type, before
    /// returning it.
    ///
    /// # Validation
    ///
    /// This validation is informed by the argument `v`, which is a generic type `V`
    /// satisfying the trait bounds [`TagValidator<U>`](crate::parse::error::TagValidator).
    ///
    /// Currently, `TagValidator<U>` is implemented for arrays, slices, and vectors containing
    /// all `U` values that are legal as discriminants for the type `T`
    ///
    /// # Invariants
    ///
    /// All implementations must uphold the contract that the only possible return values
    /// are `Err(_)`, and `Ok(val)` for some `val` in `valid`.
    fn take_tagword<T, U, V>(&mut self, v: V) -> ParseResult<U>
    where
        U: error::TagType + crate::conv::Decode,
        Self: Sized,
        V: error::TagValidator<U>,
    {
        let actual: U = crate::conv::Decode::parse(self)?;
        if v.is_valid(actual) {
            Ok(actual)
        } else if v.has_valid() {
            Err(U::promote(TagError::new(
                actual,
                std::any::type_name::<T>(),
                Some(v.into_valid()),
            )))
        } else {
            Err(ParseError::Internal(InternalError::NoValidTags))
        }
    }

    /// Consumes and returns a `Vec<u8>` of length `nbytes`, following
    /// the same behavioral guarantees as [`consume`].
    ///
    /// The default implementation is to call `consume` and convert the
    /// resulting slice into a `Vec<u8>`.
    #[inline]
    fn take_dynamic(&mut self, nbytes: usize) -> ParseResult<Vec<u8>> {
        self.consume(nbytes).map(Vec::from)
    }

    /// Consumes and returns an array of the constant length `N`
    ///
    /// The default implementation is a bare call to [`consume_arr`]
    fn take_fixed<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
        self.consume_arr::<N>()
    }

    /// Consumes bytes until the predicate `is_terminal` is satisfied,
    /// returning a `Vec<u8>` consisting of all the bytes that were
    /// consumed, up until and including the first byte that satisfied
    /// the predicate.
    ///
    /// If the predicate has not been satisfied by the time no additional bytes
    /// can be legally consumed, returns an error.
    ///
    /// This is primarily intended for the schema-inherent self-terminating
    /// Zarith types [`N`](crate::zarith::n::N) and [`Z`](crate::zarith::z::Z).
    ///
    fn take_self_terminating<F>(&mut self, is_terminal: F) -> ParseResult<Vec<u8>>
    where
        F: Fn(u8) -> bool,
    {
        let mut ret: Vec<u8> = Vec::with_capacity(self.remainder());
        loop {
            match self.consume_byte() {
                Ok(byte) => {
                    ret.push(byte);
                    if is_terminal(byte) {
                        break Ok(ret);
                    }
                }
                Err(_) => break Err(ParseError::from(TokenError::NonTerminating(ret))),
            }
        }
    }

    /// Validates and returns a representation of the final state of a `Parser` object.
    ///
    /// The receiver is passed in by value, so that this method acts in place of an
    /// implicit [`drop`] when it leaves scope.
    ///
    /// Unless any invariants on the `Parser` object fail, will return `Ok(residue)`,
    /// where `residue` contains any and all unconsumed bytes in the buffer of `self`,
    /// possibly including windowing information.
    ///
    /// # Errors
    ///
    /// Will return `Err(_)` if any of the internal method-calls on `self`
    /// return an unexpected error; namely, any error that indicates that either
    /// the state of the `Parser` is somehow malformed, or certain methods might
    /// have implementation bugs.
    fn cleanup(self) -> cleanup::CleanupResult;
}

pub mod buffer;

pub mod cleanup {
    //! End-of-lifetime cleanup for `Parser` objects
    //!
    //! This module provides the necessary logic to allow for invariant-checking
    //! on leftover state of `Parser` that would be unsound or unwise to perform
    //! in the [`Drop::drop`] implementation.
    //!
    //! This module defines the `LeftoverState` type that represents the
    //! context-preserving unconsumed portion of a to-be-discarded `Parser`
    //! value. It also defines the error-type `InvariantError`, which
    //! encapsulates any unanticipated errors returned while processing
    //! the leftover state of the `Parser` object in question.

    use crate::internal::splitvec::SplitVec;

    /// Residual state of a `Parser` type before it was dropped
    ///
    /// Preserves a record of the context windows open on the object
    /// it was constructed from.
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
    pub enum LeftoverState {
        /// Variant representing parsers with no open context windows
        /// and no residual (unconsumed) bytes
        Empty,
        /// Variant representing parsers with no open context windows,
        /// but almost certainly at least one residual (unconsumed) byte.
        ///
        /// It is techincally possible for [`Windowless`] to contain
        /// zero bytes, but this is an incoherent state, and should
        /// not normally be produced.
        Windowless(Vec<u8>),
        /// Variant representing parsers with at least one open context
        /// window, but which may or may not have any residual (unconsumed)
        /// bytes.
        Windowed(SplitVec<u8>),
    }

    impl std::default::Default for LeftoverState {
        /// Returns the default value of [`Empty`]
        #[inline]
        fn default() -> Self {
            Self::Empty
        }
    }

    impl LeftoverState {
        // Returns a new `LeftoverState` value, initially [`Empty`]
        #[inline(always)]
        pub fn new() -> Self {
            Self::Empty
        }

        /// Moves the bytes stored in `other` into `self`, promoting from
        /// [`Empty`] to [`Windowed`] and otherwise acting directly on the held
        /// value of each variant.
        ///
        /// After this call, `other` is left empty.
        #[inline]
        pub fn append(&mut self, other: &mut Vec<u8>) {
            match self {
                LeftoverState::Empty => {
                    *self = Self::Windowless(other.clone());
                }
                LeftoverState::Windowless(buf) => buf.append(other),
                LeftoverState::Windowed(sbuf) => sbuf.append_current(other),
            }
        }

        /// Returns a mutable reference to the `SplitVec<u8>` contained within
        /// a [`Windowed`] variant, without modifying `self` directly.
        ///
        /// # Safety
        ///
        /// This function is designed and optimized around the promise
        /// that it will only ever be called on `Windowed` variants.
        /// Calling this method on any other variant is ***undefined
        /// behavior*** and should only ever be called when there is
        /// an absolute guarantee that the variant held by the receiver
        /// at call-time is `Windowed`.
        #[must_use]
        unsafe fn get_mut_windows_unchecked(&mut self) -> &mut SplitVec<u8> {
            if let Self::Windowed(ref mut sbuf) = self {
                sbuf
            } else {
                std::hint::unreachable_unchecked()
            }
        }

        /// Extracts the `Vec<u8>` stored in a [`Windowless`] variant,
        /// leaving [`Empty`] behind in `self`.
        ///
        /// # Safety
        ///
        /// This function is designed and optimized around the promise
        /// that it will only ever be called on `Windowless` variants.
        /// Calling this method on any other variant is ***undefined
        /// behavior*** and should only ever be called when there is
        /// an absolute guarantee that the variant held by the receiver
        /// at call-time is `Windowless`.
        #[must_use]
        unsafe fn take_vec_unchecked(&mut self) -> Vec<u8> {
            let mut tmp = Self::Empty;
            std::mem::swap(self, &mut tmp);
            if let Self::Windowless(buf) = tmp {
                buf
            } else {
                std::hint::unreachable_unchecked()
            }
        }

        fn promote(&mut self) -> &mut SplitVec<u8> {
            match self {
                LeftoverState::Empty => {
                    *self = Self::Windowed(SplitVec::new());
                }
                &mut LeftoverState::Windowless(_) => {
                    *self =
                        Self::Windowed(SplitVec::from_vec(unsafe { self.take_vec_unchecked() }));
                }
                LeftoverState::Windowed(_) => {}
            }
            unsafe { self.get_mut_windows_unchecked() }
        }

        #[inline]
        pub fn escape_context(&mut self) {
            self.promote().split_force();
        }

        /// Returns `true` when `self` contains no leftover bytes
        ///
        /// This usually applies only for the [`Empty`] constructor,
        /// but for completeness, [`Windowed`] and [`Windowless`]
        /// constructors that contain no bytes also yield `true`.
        #[inline]
        pub fn is_empty(&self) -> bool {
            match self {
                LeftoverState::Empty => true,
                /* NOTE: the following two cases are not expected to ever arise, but are handled for completeness */
                LeftoverState::Windowed(sbuf) => sbuf.is_empty(),
                LeftoverState::Windowless(buf) => buf.is_empty(),
            }
        }

        /// Returns the number of leftover bytes stored in `self`, irrespective
        /// of windowing
        ///
        /// Returns `0` for [`Empty`], and otherwise returns the number of bytes
        /// in a `Windowed` or `Windowless` variant.
        #[inline]
        pub fn len(&self) -> usize {
            match self {
                LeftoverState::Empty => 0,
                LeftoverState::Windowless(v) => v.len(),
                LeftoverState::Windowed(sv) => sv.len(),
            }
        }
    }

    #[derive(Clone)]
    pub enum InvariantError {
        ErrorCaseUnexpected(super::error::WindowError),
        ErrorKindUnexpected(super::error::ParseError),
        ErrorUnexpected(super::error::ParseError),
    }

    impl std::fmt::Debug for InvariantError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::ErrorCaseUnexpected(err) => {
                    write!(f, "unexpected WindowError variant encountered: {:?}", err)
                }
                Self::ErrorKindUnexpected(err) => {
                    write!(
                        f,
                        "error of unexpected kind (non-WindowError) encountered: {:?}",
                        err
                    )
                }
                Self::ErrorUnexpected(err) => {
                    write!(f, "unexpected error encountered: {:?}", err)
                }
            }
        }
    }

    impl std::fmt::Display for InvariantError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                InvariantError::ErrorCaseUnexpected(e) => {
                    write!(f, "unexpected window-error case: {}", e)
                }
                InvariantError::ErrorKindUnexpected(e) => {
                    write!(f, "unexpected non-window error: {}", e)
                }
                InvariantError::ErrorUnexpected(e) => {
                    write!(f, "unexpected error: {}", e)
                }
            }
        }
    }

    impl std::error::Error for InvariantError {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            match self {
                InvariantError::ErrorCaseUnexpected(err) => Some(err),
                InvariantError::ErrorKindUnexpected(err) => Some(err),
                InvariantError::ErrorUnexpected(err) => Some(err),
            }
        }
    }

    pub type CleanupResult = std::result::Result<LeftoverState, InvariantError>;
}

macro_rules! impl_iterator_parser {
    ( $t:ty ) => {
        impl Iterator for $t {
            type Item = u8;

            fn next(&mut self) -> Option<Self::Item> {
                <$t as $crate::parse::Parser>::consume_byte(self).ok()
            }
        }
    };
}

pub(self) use impl_iterator_parser;

pub mod byteparser {
    use crate::internal::offset::{ContextOffset, IndexTracker};

    use super::buffer::VecBuffer;
    use super::cleanup::{CleanupResult, InvariantError, LeftoverState};
    use super::error::{ParseError, ParseResult};
    use super::Parser;

    #[derive(Debug)]
    pub struct ByteParser {
        buffer: VecBuffer,
        offset: ContextOffset,
    }

    impl Parser for ByteParser {
        type Buffer = VecBuffer;

        /// Create a `ByteParser` from any buffer type, i.e. any type `T` that
        /// satisfies `OwnedBytes: From<T>`.
        ///
        /// The resulting parser will have an offset of 0 and no context windows
        /// at time of creation.
        fn from_buffer(buffer: Self::Buffer) -> Self {
            let offset = ContextOffset::with_limit(buffer.len());
            Self { buffer, offset }
        }

        /// Computes the length of the current view of the `ByteParser`'s buffer.
        #[inline]
        #[must_use]
        fn view_len(&self) -> usize {
            self.offset.limit()
        }

        #[inline]
        #[must_use]
        fn offset(&self) -> usize {
            self.offset.index()
        }

        fn consume_byte(&mut self) -> ParseResult<u8> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                Ok(self.buffer.get_byte(ix))
            } else {
                Err(ParseError::Window(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset: ix,
                        requested: 1,
                        limit: self.view_len(),
                    },
                ))
            }
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            let (ix, adv) = self.offset.advance(nbytes);
            if adv {
                Ok(unsafe { self.buffer.get_slice_unchecked(ix, nbytes) })
            } else {
                Err(ParseError::Window(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset: ix,
                        requested: nbytes,
                        limit: self.view_len(),
                    },
                ))
            }
        }

        #[inline]
        fn set_fit(&mut self, n: usize) -> ParseResult<()> {
            self.offset.set_fit(n)
        }

        #[inline]
        fn test_target(&mut self) -> ParseResult<bool> {
            self.offset.test_target()
        }

        #[inline]
        fn enforce_target(&mut self) -> ParseResult<()> {
            self.offset.enforce_target()
        }

        fn cleanup(mut self) -> CleanupResult {
            use crate::parse::error::*;

            let mut ret = Ok(LeftoverState::Empty);

            loop {
                let res = self.remainder();
                if res != 0 {
                    match self.take_dynamic(res) {
                        Ok(ref mut tmp) => {
                            if let Ok(o) = &mut ret {
                                o.append(tmp)
                            }
                        }
                        Err(e) => {
                            ret = Err(InvariantError::ErrorUnexpected(e));
                            break;
                        }
                    }
                }
                match self.enforce_target() {
                    Ok(()) => {
                        if let Ok(o) = &mut ret {
                            o.escape_context()
                        }
                    }
                    Err(e) => {
                        if let ParseError::Window(w_err) = e {
                            match w_err {
                                WindowError::CloseWithoutWindow => break,
                                _ => ret = Err(InvariantError::ErrorCaseUnexpected(w_err)),
                            }
                        } else {
                            ret = Err(InvariantError::ErrorKindUnexpected(e));
                        }
                    }
                }
            }
            ret
        }
    }

    super::impl_iterator_parser!(ByteParser);
}

pub mod memoparser {
    use crate::internal::offset::{ContextOffset, IndexTracker};
    use crate::internal::splitvec::SplitVec;

    use super::buffer::VecBuffer;
    use super::cleanup::{CleanupResult, InvariantError, LeftoverState};
    use super::error::{ParseError, ParseResult};
    use super::Parser;

    #[derive(Debug)]
    pub struct MemoParser {
        buffer: VecBuffer,
        offset: ContextOffset,
        munches: Vec<usize>,
    }

    macro_rules! eprint_munches {
        ($self:expr) => {{
            let mut splits = SplitVec::new();
            let mut ix: usize = 0;
            for &len in $self.munches.iter() {
                let tmp: &[u8] = $self.buffer.get_slice(ix, len);
                splits.extend_current(tmp.iter().copied());
                splits.split();
                ix += len;
            }
            eprintln!("{}", splits);
        }};
    }

    impl Parser for MemoParser {
        type Buffer = VecBuffer;

        /// Create a `MemoParser` from any buffer type, i.e. any type `T` that
        /// satisfies `OwnedBytes: From<T>`.
        ///
        /// The resulting parser will have an offset of 0 and no context windows
        /// at time of creation.
        fn from_buffer(buffer: Self::Buffer) -> Self {
            let offset = ContextOffset::with_limit(buffer.len());
            let munches = Vec::new();
            Self {
                buffer,
                offset,
                munches,
            }
        }

        #[inline]
        fn view_len(&self) -> usize {
            self.offset.limit()
        }

        #[inline]
        fn offset(&self) -> usize {
            self.offset.index()
        }

        fn consume_byte(&mut self) -> ParseResult<u8> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                self.munches.push(1);
                Ok(self.buffer.get_byte(ix))
            } else {
                let offset = ix;
                eprint_munches!(self);
                Err(ParseError::Window(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset,
                        requested: 1,
                        limit: self.view_len(),
                    },
                ))
            }
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            let (ix, adv) = self.offset.advance(nbytes);
            if adv {
                self.munches.push(nbytes);
                Ok(unsafe { self.buffer.get_slice_unchecked(ix, nbytes) })
            } else {
                let offset = ix;
                eprint_munches!(self);
                Err(ParseError::Window(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset,
                        requested: nbytes,
                        limit: self.view_len(),
                    },
                ))
            }
        }

        #[inline]
        fn set_fit(&mut self, n: usize) -> ParseResult<()> {
            self.offset.set_fit(n)
        }

        #[inline]
        fn test_target(&mut self) -> ParseResult<bool> {
            self.offset.test_target()
        }

        #[inline]
        fn enforce_target(&mut self) -> ParseResult<()> {
            self.offset.enforce_target()
        }

        fn cleanup(mut self) -> CleanupResult {
            use crate::parse::error::*;

            let mut ret = Ok(LeftoverState::new());

            loop {
                let res = self.remainder();
                if res != 0 {
                    match self.take_dynamic(res) {
                        Ok(ref mut tmp) => {
                            if let Ok(o) = &mut ret {
                                o.append(tmp);
                            }
                        }
                        Err(e) => {
                            ret = Err(InvariantError::ErrorUnexpected(e));
                            break;
                        }
                    }
                }
                match self.enforce_target() {
                    Ok(()) => {
                        if let Ok(o) = &mut ret {
                            o.escape_context();
                        }
                    }
                    Err(e) => {
                        if let ParseError::Window(w_err) = e {
                            match w_err {
                                WindowError::CloseWithoutWindow => break,
                                _ => ret = Err(InvariantError::ErrorCaseUnexpected(w_err)),
                            }
                        } else {
                            ret = Err(InvariantError::ErrorKindUnexpected(e));
                        }
                    }
                }
            }
            ret
        }
    }

    super::impl_iterator_parser!(MemoParser);
}

pub mod sliceparser {
    use super::buffer::SliceBuffer;
    use super::cleanup::{CleanupResult, InvariantError, LeftoverState};
    use super::error::{ParseError, ParseResult, WindowError};
    use super::Parser;
    use crate::internal::view::ViewStack;
    use crate::internal::Stack;

    #[derive(Debug)]
    pub struct SliceParser<'a> {
        view_stack: ViewStack<'a>,
    }

    impl<'a> Parser for SliceParser<'a> {
        type Buffer = SliceBuffer<'a>;

        /// Construct a `SliceParser<'a>` over a buffer created by an infallible
        /// conversion from `T` to `ByteSlice<'a>`
        ///  that can be infallibly converted into a `ByteSlice` value into
        /// a SliceParser over said slice.
        ///
        /// If any error is encountered during conversion into the `ByteSlice`, this function
        /// will panic with that error as its displayed exception context.
        fn from_buffer(buffer: Self::Buffer) -> Self {
            Self {
                view_stack: ViewStack::from_buffer(buffer),
            }
        }

        #[inline]
        fn view_len(&self) -> usize {
            match self.view_stack.peek() {
                Some(bs) => bs.len(),
                None => 0,
            }
        }

        #[inline(always)]
        fn offset(&self) -> usize {
            0
        }

        #[inline(always)]
        fn remainder(&self) -> usize {
            self.view_len()
        }

        fn consume_byte(&mut self) -> ParseResult<u8> {
            match Stack::peek_mut(&mut self.view_stack) {
                None => Err(ParseError::Window(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset: 0,
                        requested: 1,
                        limit: 0,
                    },
                )),
                Some(frame) => {
                    if let Some((ret, temp)) = frame.cut_first() {
                        *frame = temp;
                        Ok(ret)
                    } else {
                        Err(ParseError::Window(
                            super::error::WindowError::ConsumeWouldExceedLimit {
                                offset: 0,
                                requested: 1,
                                limit: 0,
                            },
                        ))
                    }
                }
            }
        }

        fn consume(&mut self, nbytes: usize) -> ParseResult<&[u8]> {
            match self.view_stack.peek_mut() {
                None => Err(ParseError::Window(WindowError::ConsumeWouldExceedLimit {
                    offset: 0,
                    requested: nbytes,
                    limit: 0,
                })),
                Some(frame) => {
                    let limit = frame.len();
                    if limit >= nbytes {
                        unsafe {
                            let (ret, temp) = frame.take_unchecked(nbytes);
                            *frame = temp;
                            Ok(ret)
                        }
                    } else {
                        Err(ParseError::Window(WindowError::ConsumeWouldExceedLimit {
                            limit,
                            requested: nbytes,
                            offset: 0,
                        }))
                    }
                }
            }
        }

        fn set_fit(&mut self, n: usize) -> std::result::Result<(), ParseError> {
            match self.view_stack.peek_mut() {
                None if n == 0 => Ok(()),
                None => Err(ParseError::Window(WindowError::OpenWouldExceedBuffer {
                    bytes_left: 0,
                    request: n,
                })),
                Some(frame) => {
                    if frame.len() >= n {
                        unsafe {
                            let (novel, rem) = frame.split_unchecked(n);
                            *frame = rem;
                            self.view_stack.push_unchecked(novel);
                            Ok(())
                        }
                    } else {
                        Err(ParseError::Window(WindowError::OpenWouldExceedWindow {
                            limit: frame.len(),
                            request: n,
                        }))
                    }
                }
            }
        }

        #[inline]
        fn test_target(&mut self) -> ParseResult<bool> {
            if let Some(t) = self.view_stack.peek() {
                Ok(t.is_empty())
            } else {
                Ok(false)
            }
        }

        fn enforce_target(&mut self) -> ParseResult<()> {
            let _window = self.view_stack.pop();
            match _window {
                None => Err(ParseError::Window(WindowError::CloseWithoutWindow)),
                Some(_frame) => match _frame.len() {
                    0 => Ok(()),
                    residual => Err(ParseError::Window(WindowError::CloseWithResidue {
                        residual,
                    })),
                },
            }
        }

        fn cleanup(mut self) -> CleanupResult {
            let mut ret = Ok(LeftoverState::new());

            loop {
                let res = self.remainder();
                if res != 0 {
                    match self.take_dynamic(res) {
                        Ok(ref mut tmp) => {
                            if let Ok(o) = &mut ret {
                                o.append(tmp);
                            }
                        }
                        Err(e) => {
                            ret = Err(InvariantError::ErrorUnexpected(e));
                            break;
                        }
                    }
                }
                match self.enforce_target() {
                    Ok(()) => {
                        if let Ok(o) = &mut ret {
                            o.escape_context();
                        }
                    }
                    Err(e) => {
                        if let ParseError::Window(w_err) = e {
                            match w_err {
                                WindowError::CloseWithoutWindow => break,
                                _ => ret = Err(InvariantError::ErrorCaseUnexpected(w_err)),
                            }
                        } else {
                            ret = Err(InvariantError::ErrorKindUnexpected(e));
                        }
                    }
                }
            }
            ret
        }
    }

    super::impl_iterator_parser!(SliceParser<'_>);
}

use byteparser::ByteParser;

use crate::conv::error::DecodeError;

use self::error::TokenError;

/// Helper trait marking types that can be converted (possibly fallibly),
/// into `Parser` objects of the specified type.
///
/// When no generic argument is provided, the default `Parser` type
/// used is [`ByteParser`]
pub trait TryIntoParser<P = ByteParser>
where
    P: Parser,
{
    type Error: Into<DecodeError>;

    /// Attempt to produce a parser object of type `P` over the bytes
    /// represented by `self`.
    ///
    /// # Errors
    ///
    /// This function will return an error if the conversion from `self`
    /// into the buffer-type of `P` failed.
    ///
    /// This is normally only possible when the feature-flag `implicit_hexstring`
    /// is turned on, as otherwise the conversions defined within this library
    /// are all infallible.
    fn try_into_parser(self) -> std::result::Result<P, Self::Error>;
}

impl<P, T> TryIntoParser<P> for T
where
    P: Parser,
    <P as Parser>::Buffer: TryFrom<T>,
    DecodeError: From<<T as TryInto<<P as Parser>::Buffer>>::Error>,
{
    type Error = <T as TryInto<<P as Parser>::Buffer>>::Error;

    fn try_into_parser(self) -> std::result::Result<P, Self::Error> {
        let buffer = match <<P as Parser>::Buffer as TryFrom<T>>::try_from(self) {
            Ok(x) => x,
            Err(err) => return Err(err),
        };
        Ok(P::from_buffer(buffer))
    }
}
