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
    /// The standard buffer type a new `Parser` object can be infallibly
    /// instantiated from.
    ///
    /// Typically will be one of [`bytes::OwnedBytes`] or [`bytes::ByteSlice<'a>`],
    /// but may have other values for more exotic or specialized Parser types.
    type Buffer;

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
    fn remainder(&self) -> usize {
        self.view_len() - self.offset()
    }

    /// Consumes and returns a single byte from the current offset position
    /// in the buffer.
    ///
    /// This method should be functionally equivalent to [`consume`] call of
    /// length `1`, aside from the different return types.
    fn consume_byte(&mut self) -> ParseResult<u8>;

    /// Consumes and returns a slice of length `nbytes`
    /// continuing from the  from the current offset of the buffer.
    ///
    /// It is required that if the result of this function is `Ok(s)`,
    /// then `s.len() == nbytes`. Failure to guarantee this is
    /// an implementation bug.
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

    /// Attempts to close the current context-window.
    ///
    /// This method must fail when there are no context windows left unclosed,
    /// or when there is at least one byte remaining in the current context window.
    ///
    /// It is considered impossible for `enforce_target` to encounter a situation in
    /// which the offset has advanced beyond the current context window, though such
    /// a case may be tested for by implementors.
    fn enforce_target(&mut self) -> ParseResult<()>;

    /// Consumes `N` bytes and returns them in array-form
    ///
    /// # Panics
    ///
    /// This function will only panic if [`consume`] is not implemented
    /// correctly, which indicates an fundamental implementation bug,
    /// rather than any sort of preconditon violations on the caller side.
    fn consume_arr<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
        error::coerce_slice(self.consume(N)?)
    }

    /// Consumes one byte and returns it as a `u8` value
    #[inline]
    fn take_u8(&mut self) -> ParseResult<u8> {
        self.consume_byte()
    }

    /// Consumes one byte and returns it as an `i8` value
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
    /// the coercion as big-endian.
    #[inline]
    fn take_u32(&mut self) -> ParseResult<u32> {
        self.consume_arr::<4>().map(u32::from_be_bytes)
    }

    /// Consumes four bytes and returns the corresponding `i32` value
    ///
    /// As with all fixed-width numeric `take_X` methods, this method performs
    /// an implicitly big-endian conversion with respect to the individual bytes
    /// consumed.
    #[inline]
    fn take_i32(&mut self) -> ParseResult<i32> {
        self.consume_arr::<4>().map(i32::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `u64` value
    ///
    /// As with all fixed-width numeric `take_X` methods, this method performs
    /// an implicitly big-endian conversion with respect to the individual bytes
    /// consumed.
    #[inline]
    fn take_u64(&mut self) -> ParseResult<u64> {
        self.consume_arr::<8>().map(u64::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `f64` value
    ///
    /// As with all fixed-width numeric `take_X` methods, this method performs
    /// an implicitly big-endian conversion with respect to the individual bytes
    /// consumed.
    #[inline]
    fn take_f64(&mut self) -> ParseResult<f64> {
        self.consume_arr::<8>().map(f64::from_be_bytes)
    }

    /// Consumes eight bytes and returns the corresponding `i64` value
    ///
    /// As with all `take_uX` and `take_iX` methods, this method performs
    /// the coercion as big-endian.
    #[inline]
    fn take_i64(&mut self) -> ParseResult<i64> {
        self.consume_arr::<8>().map(i64::from_be_bytes)
    }

    /// Consumes a single byte and returns the boolean value it represents
    ///
    /// According to the binary schema used in `data-encoding`,
    /// the only valid boolean encodings are `0xff` for `true`
    /// and `0x00` for false.
    ///
    /// If the consumed byte is not a valid boolean, or if the consume operation
    /// itself was unsuccessful, an error is returned instead.
    #[inline]
    fn take_bool(&mut self) -> ParseResult<bool> {
        match self.consume_byte()? {
            0xff => Ok(true),
            0x00 => Ok(false),
            byte => Err(ParseError::TokenError(TokenError::InvalidBoolean(byte))),
        }
    }

    /// Parses a `u8`, `u16`, or `u32` (determined by the second generic parameter `U`),
    /// validating it against the slice `valid` containing all legal tag-values for
    /// the discriminated type `T`.
    ///
    /// All implementations must uphold the contract that the only possible return values
    /// are `Err(_)`, and `Ok(val)` for some `val` in `valid`.
    fn take_tagword<T, U, V>(&mut self, validator: V) -> ParseResult<U>
    where
        U: error::TagType + crate::conv::Decode,
        Self: Sized,
        V: error::TagValidator<U>,
    {
        if validator.has_valid() {
            return Err(ParseError::InternalError(InternalError::NoValidTags));
        }
        let actual: U = crate::conv::Decode::parse(self)?;
        if validator.validate(actual) {
            Ok(actual)
        } else {
            Err(<U as error::TagType>::promote(TagError::new(
                actual,
                std::any::type_name::<T>(),
                Some(validator.into_valid())
            )))
        }
    }

    #[inline]
    fn take_dynamic(&mut self, nbytes: usize) -> ParseResult<Vec<u8>> {
        self.consume(nbytes).map(Vec::from)
    }

    fn take_fixed<const N: usize>(&mut self) -> ParseResult<[u8; N]> {
        self.consume_arr::<N>()
    }

    fn take_self_terminating<F>(&mut self, is_terminal: F) -> ParseResult<Vec<u8>>
    where
        F: Fn(u8) -> bool,
    {
        let mut ret: Vec<u8> = Vec::with_capacity(self.view_len() - self.offset());
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
}

pub mod bytes {
    use crate::hexstring::HexString;

    /// Newtype around a lifetime-annotated immutable reference `&'a [u8]`
    ///
    /// There is no overwhelming motivation for a full newtype,
    /// other than to prevent overlapping instances for different interpretations
    /// of what sort of role `&[u8]` plays in the context of the runtime.
    ///
    /// In this case, `ByteSlice` is explicitly used only as the buffer type for
    /// a slice-based [`Parser`], and is not to be used in place of `&'a [u8]` in
    /// any other context.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct ByteSlice<'a>(&'a [u8]);

    impl ByteSlice<'_> {
        /// Creates an explicitly static `ByteSlice` from a static slice
        pub const fn from_static(slice: &'static [u8]) -> ByteSlice<'static> {
            ByteSlice(slice)
        }
    }

    impl<'a> ByteSlice<'a> {
        /// Extracts a copy of the internal `&'a [u8]` of a borrowed `ByteSlice`
        ///
        /// Aside from signature, this is identical to [`into_slice`].
        pub const fn as_slice(&self) -> &'a [u8] {
            self.0
        }

        /// Destructs `self` and returns the `&'a [u8]` it contained
        ///
        /// Aside from signature, this is identical to [`as_slice`].
        pub const fn into_slice(self) -> &'a [u8] {
            self.0
        }

        /// Returns `true` if the `ByteSlice` has a length of 0
        pub const fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        /// Returns the number of bytes in a ByteSlice.
        #[inline(always)]
        pub const fn len(&self) -> usize {
            self.0.len()
        }

        /// Creates a `ByteSlice` from a slice, using the same lifetime annotation
        pub const fn new(slice: &'a [u8]) -> Self {
            Self(slice)
        }

        /// Attempt to split off the head byte of a `ByteSlice`
        ///
        /// Returns `None` if the `ByteSlice` is empty
        ///
        /// Otherwise, returns `Some()
        ///
        /// # Panics
        ///
        pub const fn pop_first(&self) -> Option<(u8, Self)> {
            if let [first, tail @ ..] = self.0 {
                Some((*first, Self(tail)))
            } else {
                None
            }
        }

        /// Splits off the head byte of a `ByteSlice` without checking that it is non-empty
        ///
        /// # Safety
        ///
        /// Calling this method on an empty `ByteSlice` is *[undefined behavior]*.
        ///
        /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
        pub unsafe fn pop_first_unchecked(&self) -> (u8, Self) {
            (*self.0.get_unchecked(0), Self(self.0.get_unchecked(1..)))
        }

        /// Splits a `ByteSlice` into the segments containing indices `[0..mid]` and `[mid..]`,
        /// as `ByteSlice`
        ///
        /// This function should behave no differently from [`split_at`][splitat]
        ///
        /// [splitat]: https://doc.rust-lang.org/stable/std/primitive.slice.html#method.split_at
        pub fn split(&self, mid: usize) -> (Self, Self) {
            assert!(mid <= self.len());
            unsafe { self.split_unchecked(mid) }
        }

        /// Splits a `ByteSlice` into the segments containing indices `[0..mid]` and `[mid..]`,
        /// as `ByteSlice`, without doing any bounds-checking.
        ///
        /// This is equivalent to [`take_unchecked`] with a wrapped first return value
        ///
        /// # Safety
        ///
        /// Calling this method with `n > self.len()` is *[undefined behavior]*
        /// even if the return value is unused.
        ///
        /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
        pub unsafe fn split_unchecked(&self, mid: usize) -> (Self, Self) {
            (
                Self(self.0.get_unchecked(..mid)),
                Self(self.0.get_unchecked(mid..)),
            )
        }

        /// Extracts the first `N` indices of a `ByteSlice` and return them
        /// as a slice, along with the remainder as a `ByteSlice`
        ///
        /// This function is only `unsafe` because it does not itself perform
        /// any slice-length bound-checking and will therefore panic as normal
        /// when the number of indices to take exceeds the number of indices
        /// in the slice itself.
        pub fn take(&self, n: usize) -> (&'a [u8], Self) {
            assert!(n <= self.len());
            unsafe { self.take_unchecked(n) }
        }

        /// Extracts the first `len` indices of a `ByteSlice` unwrapped,
        /// along with the remainder as a `ByteSlice`, without
        /// doing bounds-checking.
        ///
        /// For a safe alternative see [`take`]
        ///
        /// # Safety
        ///
        /// Calling this method with `n > self.len()` is *[undefined behavior]*
        /// even if the return value is unused.
        ///
        /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
        pub unsafe fn take_unchecked(&self, n: usize) -> (&'a [u8], Self) {
            (self.0.get_unchecked(..n), Self(self.0.get_unchecked(n..)))
        }
    }

    impl<'a> From<&'a [u8]> for ByteSlice<'a> {
        #[inline]
        fn from(bytes: &'a [u8]) -> Self {
            Self(bytes)
        }
    }

    /// Newtype around a monomorphized `Vec<u8>`
    ///
    /// There is no overwhelming motivation for having this type be separate,
    /// other than to prevent overlapping instances for different interpretations
    /// of what sort of role `Vec<u8>` plays in the context of the runtime.
    ///
    /// In this case, `OwnedBytes` is explicitly used only as the buffer type for
    /// a vector-based [`Parser`], and is not to be used in place of `Vec<u8>` in
    /// any other context.
    #[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct OwnedBytes(Vec<u8>);

    impl OwnedBytes {
        /// Returns the length of the vector enclosed by an OwnedBytes value.
        pub fn len(&self) -> usize {
            self.0.len()
        }

        /// Returns `true` if the buffer contains zero bytes
        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        /// Borrows a range of bytes starting at index `ix`, of length `len`,
        /// without bounds-checking.
        ///
        /// # Safety
        ///
        /// Calling this method when `[ix..ix + len]` is not in-bounds is
        /// *[undefined behavior]* even if the return value is not used.
        ///
        /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
        pub unsafe fn get_slice_unchecked(&self, ix: usize, len: usize) -> &[u8] {
            self.0.get_unchecked(ix..ix + len)
        }

        /// Borrows a range of bytes starting at index `ix`, of length `len`.
        ///
        /// # Safety
        ///
        /// This function is marked as `unsafe` to ensure that the caller is certain
        /// that the attempted slice access will not violate the bounds of the vector
        /// wrapped inside the receiver. If this guarantee is not made, this function
        /// will panic as usual, but does not itself perform any bounds validation beyond
        /// what Rust itself performs when attempting to borrow a range of indices of
        /// a vector as a slice.
        pub fn get_slice(&self, ix: usize, len: usize) -> &[u8] {
            assert!(ix + len <= self.len());
            unsafe { self.get_slice_unchecked(ix, len) }
        }

        /// Returns the byte at the specified index without checking that it is in-bounds.
        ///
        /// # Safety
        ///
        /// Calling this method with an out-of-bonds index is
        /// *[undefined behavior]* even if the return value is not used.
        ///
        /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
        pub unsafe fn get_byte_unchecked(&self, ix: usize) -> u8 {
            *self.0.get_unchecked(ix)
        }

        /// Returns the byte at the specified index,
        ///
        /// # Panics
        ///
        /// Will panic if the index is out of bounds
        pub fn get_byte(&self, ix: usize) -> u8 {
            assert!(ix <= self.len());
            unsafe { self.get_byte_unchecked(ix) }
        }
    }

    impl std::fmt::Debug for OwnedBytes {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            <Vec<u8> as std::fmt::Debug>::fmt(&self.0, f)
        }
    }

    impl From<&[u8]> for OwnedBytes {
        fn from(bytes: &[u8]) -> Self {
            Self(bytes.to_owned())
        }
    }

    impl From<Vec<u8>> for OwnedBytes {
        fn from(bytes: Vec<u8>) -> Self {
            Self(bytes)
        }
    }

    impl<const N: usize> From<[u8; N]> for OwnedBytes {
        fn from(bytes: [u8; N]) -> Self {
            Self(bytes.to_vec())
        }
    }

    impl<const N: usize> From<&'_ [u8; N]> for OwnedBytes {
        fn from(bytes: &'_ [u8; N]) -> Self {
            Self(bytes.to_vec())
        }
    }

    impl From<HexString> for OwnedBytes {
        fn from(hex: HexString) -> Self {
            Self(hex.into_vec())
        }
    }

    macro_rules! string_to_ownedbytes {
        ( $src:ty ) => {
            #[cfg(feature = "implicit_hexstring")]
            impl std::convert::TryFrom<$src> for $crate::parse::bytes::OwnedBytes
            where
                $crate::hexstring::HexString: std::convert::TryFrom<$src>,
                $crate::parse::bytes::OwnedBytes: From<$crate::hexstring::HexString>,
            {
                type Error = <$crate::hexstring::HexString as std::convert::TryFrom<$src>>::Error;

                fn try_from(s: $src) -> Result<Self, Self::Error> {
                    Ok(<HexString as TryFrom<$src>>::try_from(s)?.into())
                }
            }

            #[cfg(not(feature = "implicit_hexstring"))]
            impl From<$src> for $crate::parse::bytes::OwnedBytes {
                fn from(s: $src) -> Self {
                    Self(s.as_bytes().to_owned())
                }
            }
        };
    }

    string_to_ownedbytes!(&'_ str);
    string_to_ownedbytes!(String);
    string_to_ownedbytes!(&'_ String);
    string_to_ownedbytes!(std::borrow::Cow<'_, str>);
}

#[cfg(not(feature = "check_parser_on_drop"))]
pub mod cleanup {
    #[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    pub enum LeftoverState {
        Empty,
        Windowless(Vec<u8>),
        Windowed(crate::internal::splitvec::SplitVec<u8>),
    }

    impl std::default::Default for LeftoverState {
        #[inline]
        fn default() -> Self {
            Self::Empty
        }
    }

    impl LeftoverState {
        #[inline]
        pub fn new() -> Self {
            Self::Empty
        }

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

        unsafe fn take_vec(&mut self) -> Vec<u8> {
            let mut tmp = Self::Empty;
            std::mem::swap(self, &mut tmp);
            if let Self::Windowless(ret) = tmp {
                ret
            } else {
                unreachable!()
            }
        }

        pub fn escape_context(&mut self) {
            match self {
                LeftoverState::Empty => {
                    let mut svec = crate::internal::SplitVec::new();
                    svec.split_force();
                    *self = Self::Windowed(svec)
                }
                LeftoverState::Windowless(_) => {
                    let buf = unsafe { self.take_vec() };
                    let mut svec = crate::internal::SplitVec::from_vec(buf);
                    svec.split_force();
                    *self = Self::Windowed(svec)
                }
                LeftoverState::Windowed(ref mut svec) => {
                    svec.split_force();
                }
            }
        }

        pub fn is_empty(&self) -> bool {
            match self {
                LeftoverState::Empty => true,
                /* NOTE: the following two cases are not expected to ever arise, but are handled for completeness */
                LeftoverState::Windowed(sbuf) => sbuf.is_empty(),
                LeftoverState::Windowless(buf) => buf.is_empty(),
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
                Self::ErrorCaseUnexpected(arg0) => {
                    f.debug_tuple("ErrorCaseUnexpected").field(arg0).finish()
                }
                Self::ErrorKindUnexpected(arg0) => {
                    f.debug_tuple("ErrorKindUnexpected").field(arg0).finish()
                }
                Self::ErrorUnexpected(arg0) => {
                    f.debug_tuple("ErrorUnexpected").field(arg0).finish()
                }
            }
        }
    }

    impl std::fmt::Display for InvariantError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                InvariantError::ErrorCaseUnexpected(wke) => {
                    write!(f, "Unexpected window-error case: {}", wke)
                }
                InvariantError::ErrorKindUnexpected(nwe) => {
                    write!(f, "Unexpected non-window error: {}", nwe)
                }
                InvariantError::ErrorUnexpected(e) => {
                    write!(f, "Unexpected error: {}", e)
                }
            }
        }
    }

    impl std::error::Error for InvariantError {}

    fn modify<T, E, F>(x: &mut Result<T, E>, mut f: F)
    where
        F: FnMut(&mut T),
    {
        match x {
            Ok(o) => f(o),
            Err(_) => (),
        }
    }

    pub type ParserStatus = std::result::Result<LeftoverState, InvariantError>;

    pub fn drop_parser(mut p: impl super::Parser) -> ParserStatus {
        use crate::parse::error::*;

        let mut ret = Ok(LeftoverState::new());

        loop {
            let res = p.remainder();
            if res != 0 {
                match p.take_dynamic(res) {
                    Ok(ref mut tmp) => {
                        modify(&mut ret, |los| los.append(tmp));
                    }
                    Err(e) => {
                        ret = Err(InvariantError::ErrorUnexpected(e));
                        break;
                    }
                }
            }
            match p.enforce_target() {
                Ok(()) => {
                    modify(&mut ret, LeftoverState::escape_context);
                }
                Err(e) => {
                    if let ParseError::WindowError(w_err) = e {
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

macro_rules! impl_drop_parser {
    (@drop) => {
        #[cfg(feature = "check_parser_on_drop")]
        fn drop(&mut self) {
                use $crate::parse::error::*;
                use $crate::parse::Parser;
                let mut incomplete: bool = false;
                let mut win_num: usize = 0;
                loop {
                    let res = self.remainder();
                    if res != 0 {
                        incomplete = true;
                        if win_num == 0 {
                            eprintln!("\x1b[1m\x1b[31mWarning\x1b[0m: A parser with at least one open context window is leaving memory...");
                        }
                        match self.get_dynamic(res) {
                            Ok(tmp) => {
                                eprintln!("\tContents of Frame #(?-{}): {:?}", win_num, tmp);
                            }
                            Err(e) => {
                                eprintln!("\tCannot display contents of frame #(?-{}): {}", win_num, e);
                            }
                        }
                    }
                    match self.enforce_target() {
                        Ok(()) => {
                            incomplete = true;
                            win_num += 1;
                        }
                        Err(e) => {
                            if let ParseError::WindowError(wek) = e {
                                match wek {
                                    WindowErrorKind::CloseWithResidue { .. } => unreachable!(),
                                    WindowErrorKind::CloseWithoutWindow => break,
                                    WindowErrorKind::OpenWouldExceedBuffer { .. } => unreachable!(),
                                    WindowErrorKind::OpenWouldExceedWindow { .. } => unreachable!(),
                                    WindowErrorKind::OffsetOverflow { .. } => {
                                        panic!(
                                            "Offset overflow detected during cleanup of dropped Parser: {}",
                                            wek
                                        );
                                    }
                                }
                            } else {
                                unreachable!();
                            }
                        }
                    }
                }
                if incomplete {
                    #[cfg(feature = "panic_on_incomplete_parse")]
                    panic!("Parser dropped before it was fully consumed (details written to stderr)!");
                }
                return;
            }

            #[cfg(not(feature = "check_parser_on_drop"))]
            fn drop(&mut self) {
                return;
            }
    };
    ($t:ty) => {
        impl Drop for $t {
            impl_drop_parser!{@drop}
        }
    };
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

pub(self) use impl_drop_parser;
pub(self) use impl_iterator_parser;

pub mod byteparser {
    use crate::internal::offset::{ContextOffset, IndexTracker};

    use super::bytes::OwnedBytes;
    use super::error::{ParseError, ParseResult};

    #[derive(Debug)]
    pub struct ByteParser {
        buffer: OwnedBytes,
        offset: ContextOffset,
    }

    impl super::Parser for ByteParser {
        type Buffer = OwnedBytes;

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

        fn consume_byte(&mut self) -> ParseResult<u8> {
            let (ix, adv) = self.offset.advance(1);
            if adv {
                Ok(self.buffer.get_byte(ix))
            } else {
                Err(ParseError::WindowError(
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
                Err(ParseError::WindowError(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset: ix,
                        requested: nbytes,
                        limit: self.view_len(),
                    },
                ))
            }
        }
    }

    super::impl_iterator_parser!(ByteParser);
    super::impl_drop_parser! {ByteParser}
}

pub mod memoparser {
    use crate::internal::offset::{ContextOffset, IndexTracker};
    use crate::internal::splitvec::SplitVec;

    use super::bytes::OwnedBytes;
    use super::error::ParseError;
    use super::ParseResult;

    #[derive(Debug)]
    pub struct MemoParser {
        buffer: OwnedBytes,
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

    impl super::Parser for MemoParser {
        type Buffer = OwnedBytes;

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
                Err(ParseError::WindowError(
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
                Err(ParseError::WindowError(
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
    }

    super::impl_iterator_parser! {MemoParser}
    super::impl_drop_parser! {MemoParser}
}

pub mod sliceparser {
    use super::{
        bytes::ByteSlice,
        error::{ParseError, ParseResult, WindowError},
    };
    use crate::internal::Stack;

    #[derive(Debug)]
    pub struct SliceParser<'a> {
        view_stack: Vec<ByteSlice<'a>>,
    }

    impl<'a> super::Parser for SliceParser<'a> {
        type Buffer = ByteSlice<'a>;

        /// Construct a `SliceParser<'a>` over a buffer created by an infallible
        /// conversion from `T` to `ByteSlice<'a>`
        ///  that can be infallibly converted into a `ByteSlice` value into
        /// a SliceParser over said slice.
        ///
        /// If any error is encountered during conversion into the `ByteSlice`, this function
        /// will panic with that error as its displayed exception context.
        fn from_buffer(buffer: Self::Buffer) -> Self {
            Self {
                view_stack: vec![buffer],
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
                None => Err(ParseError::WindowError(
                    super::error::WindowError::ConsumeWouldExceedLimit {
                        offset: 0,
                        requested: 1,
                        limit: 0,
                    },
                )),
                Some(frame) => {
                    if let Some((ret, temp)) = frame.pop_first() {
                        *frame = temp;
                        Ok(ret)
                    } else {
                        Err(ParseError::WindowError(
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
                None => Err(ParseError::WindowError(
                    WindowError::ConsumeWouldExceedLimit {
                        offset: 0,
                        requested: nbytes,
                        limit: 0,
                    },
                )),
                Some(frame) => {
                    let limit = frame.len();
                    if limit >= nbytes {
                        unsafe {
                            let (ret, temp) = frame.take_unchecked(nbytes);
                            *frame = temp;
                            Ok(ret)
                        }
                    } else {
                        Err(ParseError::WindowError(
                            WindowError::ConsumeWouldExceedLimit {
                                limit,
                                requested: nbytes,
                                offset: 0,
                            },
                        ))
                    }
                }
            }
        }

        fn set_fit(&mut self, n: usize) -> std::result::Result<(), ParseError> {
            match self.view_stack.peek_mut() {
                None if n == 0 => Ok(()),
                None => Err(ParseError::WindowError(
                    WindowError::OpenWouldExceedBuffer {
                        bytes_left: 0,
                        request: n,
                    },
                )),
                Some(frame) => {
                    if frame.len() >= n {
                        unsafe {
                            let (novel, rem) = frame.split_unchecked(n);
                            *frame = rem;
                            self.view_stack.push(novel);
                            Ok(())
                        }
                    } else {
                        Err(ParseError::WindowError(
                            WindowError::OpenWouldExceedWindow {
                                limit: frame.len(),
                                request: n,
                            },
                        ))
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
                None => Err(ParseError::WindowError(WindowError::CloseWithoutWindow)),
                Some(_frame) => match _frame.len() {
                    0 => Ok(()),
                    residual => Err(ParseError::WindowError(WindowError::CloseWithResidue {
                        residual,
                    })),
                },
            }
        }
    }

    super::impl_iterator_parser! {SliceParser<'_>}
    super::impl_drop_parser! {SliceParser<'_>}
}

use byteparser::ByteParser;

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
    fn try_into_parser(self) -> ParseResult<P>;
}

impl<P, T> TryIntoParser<P> for T
where
    P: Parser,
    <P as Parser>::Buffer: TryFrom<T>,
    <T as TryInto<<P as Parser>::Buffer>>::Error: Into<ParseError>,
{
    fn try_into_parser(self) -> ParseResult<P> {
        let buffer = match <<P as Parser>::Buffer as TryFrom<T>>::try_from(self) {
            Ok(x) => x,
            Err(err) => return Err(err.into()),
        };
        Ok(P::from_buffer(buffer))
    }
}
